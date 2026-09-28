//! Checked lowering of the finite source subset to independently verified IR.

mod basis;
mod circuit;
mod lower;
mod operations;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::ast::*;
use super::diagnostic::{Diagnostic, coordinates};
use super::project::{ImportOrigin, Project};
use crate::{VerifiedProgram, ir::Effect};

const MAX_BITS: usize = 12;
const MAX_WORK: usize = 1_000_000;
const MAX_DEPTH: usize = 64;
const MAX_TREE_NODES: usize = 4096;
const MAX_TREE_DEPTH: usize = 64;
type Key = (String, String);

/// Stable categories for consumers; `message` is explanatory text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorCode {
    Project,
    UnknownName,
    RecursiveCall,
    TypeMismatch,
    Arity,
    Ownership,
    Effect,
    InvalidEntry,
    Unsupported,
    Limit,
    InvalidIr,
    Capability,
    Contract,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileError {
    pub code: ErrorCode,
    pub path: PathBuf,
    pub span: Span,
    /// One-based Unicode character coordinates; `span` remains byte based.
    pub line: usize,
    pub column: usize,
    pub message: String,
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}:{}: {:?}: {}",
            self.path.display(),
            self.line,
            self.column,
            self.code,
            self.message
        )
    }
}

impl std::error::Error for CompileError {}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Ty {
    Unit,
    Bit,
    CBit,
    Q(Box<Ty>),
    Pair(Box<Ty>, Box<Ty>),
}

impl Ty {
    fn tree_size(&self) -> TreeSize {
        let mut size = TreeSize::default();
        let mut pending = vec![(self, 1)];
        while let Some((ty, depth)) = pending.pop() {
            size.nodes += 1;
            size.depth = size.depth.max(depth);
            match ty {
                Self::Q(inner) => pending.push((inner, depth + 1)),
                Self::Pair(a, b) => pending.extend([(a.as_ref(), depth + 1), (b, depth + 1)]),
                _ => {}
            }
        }
        size
    }

    fn basis_bits(&self) -> Option<usize> {
        match self {
            Self::Unit => Some(0),
            Self::Bit => Some(1),
            Self::Pair(a, b) => Some(a.basis_bits()? + b.basis_bits()?),
            _ => None,
        }
    }

    fn classical(&self) -> bool {
        match self {
            Self::Unit | Self::CBit => true,
            Self::Pair(a, b) => a.classical() && b.classical(),
            _ => false,
        }
    }

    fn pair(a: Self, b: Self) -> Self {
        Self::Pair(Box::new(a), Box::new(b))
    }
}

/// Count representation nodes, including zero-bit Unit products. Walking is
/// iterative so checking a newly constructed tree never needs its call depth.
#[derive(Default)]
struct TreeSize {
    nodes: usize,
    depth: usize,
}

fn total_size(sizes: impl IntoIterator<Item = usize>) -> usize {
    sizes.into_iter().fold(0, usize::saturating_add)
}

#[derive(Clone, Debug)]
enum Callee {
    User(Key),
    Sealed(String, String),
}

#[derive(Clone)]
struct BasisFunction {
    params: Vec<Ty>,
    result: Ty,
    table: Vec<u16>,
}

impl BasisFunction {
    fn signature_size(&self) -> usize {
        total_size(
            self.params
                .iter()
                .chain([&self.result])
                .map(|ty| ty.tree_size().nodes),
        )
    }
}

struct Compiler<'a> {
    project: &'a Project,
    declarations: BTreeMap<Key, &'a Decl>,
    basis: BTreeMap<Key, BasisFunction>,
    checked: BTreeMap<Key, VerifiedProgram>,
    // Private to this immutable loaded project. Dependencies are checked once
    // in topological order and never replaced, so a cache hit keeps its exact
    // source/raw binding without rescanning those frozen snapshots.
    function_evidence: BTreeMap<(Key, Key), Arc<crate::contract::FunctionEvidence>>,
    meanings: BTreeMap<Key, operations::DeclaredMeaning>,
    providers: BTreeMap<(Key, Option<Key>), operations::Operation>,
    instances: Vec<(Key, Vec<operations::Operation>)>,
    work: usize,
}

impl Compiler<'_> {
    fn error(
        &self,
        module: &str,
        span: Span,
        code: ErrorCode,
        message: impl Into<String>,
    ) -> CompileError {
        let source = &self.project.modules[module];
        let (line, column) = coordinates(&source.source, span);
        CompileError {
            code,
            path: source.path.clone(),
            span,
            line,
            column,
            message: message.into(),
        }
    }

    fn tick(&mut self, module: &str, span: Span) -> Result<(), CompileError> {
        self.charge(module, span, 1)
    }

    fn charge(&mut self, module: &str, span: Span, amount: usize) -> Result<(), CompileError> {
        if amount > MAX_WORK.saturating_sub(self.work) {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "source expansion exceeds the initial work limit",
            ));
        }
        self.work += amount;
        Ok(())
    }

    fn check_tree(&mut self, module: &str, span: Span, size: TreeSize) -> Result<(), CompileError> {
        if size.nodes > MAX_TREE_NODES || size.depth > MAX_TREE_DEPTH {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                format!("internal value or type exceeds the initial {MAX_TREE_NODES}-node / {MAX_TREE_DEPTH}-level limit"),
            ));
        }
        self.charge(module, span, size.nodes)
    }

    fn resolve(&self, module: &str, name: &Ident) -> Result<Callee, CompileError> {
        let key = (module.to_owned(), name.text.clone());
        if self.declarations.contains_key(&key) {
            return Ok(Callee::User(key));
        }
        if let Some(import) = self.project.modules[module].imports.get(&name.text) {
            return Ok(if import.origin == ImportOrigin::Sealed {
                Callee::Sealed(import.module.clone(), import.name.clone())
            } else {
                Callee::User((import.module.clone(), import.name.clone()))
            });
        }
        Err(self.error(
            module,
            name.span,
            ErrorCode::UnknownName,
            format!(
                "unknown function `{}`; standard operations require an explicit import",
                name.text
            ),
        ))
    }

    fn ty(&mut self, module: &str, ty: &Type, basis_only: bool) -> Result<Ty, CompileError> {
        let result = match &ty.kind {
            TypeKind::Unit => Ty::Unit,
            TypeKind::Bit if basis_only => Ty::Bit,
            TypeKind::CBit if !basis_only => Ty::CBit,
            TypeKind::Q(inner) if !basis_only => Ty::Q(Box::new(self.ty(module, inner, true)?)),
            TypeKind::Tuple(a, b) => Ty::pair(
                self.ty(module, a, basis_only)?,
                self.ty(module, b, basis_only)?,
            ),
            _ => {
                return Err(self.error(
                    module,
                    ty.span,
                    ErrorCode::TypeMismatch,
                    "Bit is a basis type; ordinary functions use CBit or Q<basis type>",
                ));
            }
        };
        self.check_tree(module, ty.span, result.tree_size())?;
        if basis_only && result.basis_bits().is_some_and(|bits| bits > MAX_BITS) {
            return Err(self.error(
                module,
                ty.span,
                ErrorCode::Limit,
                "basis type exceeds the initial 12-bit limit",
            ));
        }
        Ok(result)
    }

    fn signature(&mut self, key: &Key) -> Result<(Vec<Ty>, Ty), CompileError> {
        let decl = self.declarations[key];
        let mut names = BTreeSet::new();
        for param in &decl.static_params {
            if !names.insert(&param.name.text) {
                return Err(self.error(
                    &key.0,
                    param.name.span,
                    ErrorCode::Ownership,
                    "duplicate static parameter",
                ));
            }
        }
        let mut params = Vec::new();
        for param in &decl.params {
            let mut pending = vec![&param.pattern];
            while let Some(pattern) = pending.pop() {
                match &pattern.kind {
                    PatternKind::Name(name) => {
                        if !names.insert(&name.text) {
                            return Err(self.error(
                                &key.0,
                                name.span,
                                ErrorCode::Ownership,
                                "duplicate parameter name",
                            ));
                        }
                    }
                    PatternKind::Tuple(a, b) => pending.extend([b.as_ref(), a.as_ref()]),
                    PatternKind::Wildcard => {}
                }
            }
            let ty = self.ty(&key.0, &param.ty, decl.kind == FnKind::Basis)?;
            if decl.kind == FnKind::Basis && !matches!(param.pattern.kind, PatternKind::Name(_)) {
                // Reuse the coherent basis-pattern binding judgment. A zero
                // label suffices to validate shape; enumeration binds all labels.
                self.bind_basis_pattern(&key.0, &param.pattern, &ty, 0)?;
            }
            params.push(ty);
        }
        Ok((
            params,
            self.ty(&key.0, &decl.return_type, decl.kind == FnKind::Basis)?,
        ))
    }

    /// Iterative topological ordering also checks calls in unused declarations.
    fn order(&self) -> Result<Vec<Key>, CompileError> {
        let mut pending = BTreeMap::<Key, BTreeSet<Key>>::new();
        let mut users = BTreeMap::<Key, Vec<Key>>::new();
        for (key, decl) in &self.declarations {
            let mut dependencies = BTreeSet::new();
            let static_names: BTreeSet<_> =
                decl.static_params.iter().map(|p| &p.name.text).collect();
            for name in called_names(&decl.body)
                .into_iter()
                .chain(decl.static_params.iter().filter_map(|p| p.meaning.as_ref()))
            {
                if static_names.contains(&name.text) {
                    continue;
                }
                if let Callee::User(target) = self.resolve(&key.0, name)? {
                    dependencies.insert(target);
                }
            }
            for target in &dependencies {
                users.entry(target.clone()).or_default().push(key.clone());
            }
            pending.insert(key.clone(), dependencies);
        }
        let mut ready: BTreeSet<_> = pending
            .iter()
            .filter(|(_, deps)| deps.is_empty())
            .map(|(key, _)| key.clone())
            .collect();
        let mut order = Vec::new();
        while let Some(key) = ready.pop_first() {
            order.push(key.clone());
            for user in users.get(&key).into_iter().flatten() {
                let dependencies = pending.get_mut(user).expect("known caller");
                dependencies.remove(&key);
                if dependencies.is_empty() {
                    ready.insert(user.clone());
                }
            }
            pending.remove(&key);
        }
        if let Some((key, _)) = pending.first_key_value() {
            return Err(self.error(
                &key.0,
                self.declarations[key].name.span,
                ErrorCode::RecursiveCall,
                "recursive function calls are not supported",
            ));
        }
        Ok(order)
    }
}

fn effect(kind: FnKind) -> Effect {
    match kind {
        FnKind::Basis | FnKind::Meaning | FnKind::Unitary => Effect::Unitary,
        FnKind::Iso => Effect::Iso,
        FnKind::Observe => Effect::Observe,
    }
}

fn called_names(body: &FnBody) -> Vec<&Ident> {
    enum Node<'a> {
        Expr(&'a Expr),
        Basis(&'a BasisExpr),
        Block(&'a Block),
    }
    if let FnBody::Meaning { function, .. } = body {
        return vec![function];
    }
    let mut stack = vec![match body {
        FnBody::Meaning { .. } => unreachable!(),
        FnBody::Basis(expr) => Node::Basis(expr),
        FnBody::Quantum(block) => Node::Block(block),
    }];
    let mut names = Vec::new();
    while let Some(node) = stack.pop() {
        match node {
            Node::Block(block) => {
                stack.push(Node::Expr(&block.result));
                for stmt in &block.statements {
                    stack.push(Node::Expr(match &stmt.kind {
                        StmtKind::Let { value, .. } => value,
                        StmtKind::Expr(expr) => expr,
                    }));
                }
            }
            Node::Expr(expr) => match &expr.kind {
                ExprKind::ApplyContract {
                    implementation,
                    specification,
                    input,
                } => {
                    names.extend([implementation, specification]);
                    stack.push(Node::Expr(input));
                }
                ExprKind::Adjoint { function, input }
                | ExprKind::RepeatStatic {
                    function, input, ..
                } => {
                    names.push(function);
                    stack.push(Node::Expr(input));
                }
                ExprKind::QuantumIf {
                    control,
                    target,
                    zero,
                    one,
                } => {
                    names.extend([zero, one]);
                    stack.extend([Node::Expr(control), Node::Expr(target)]);
                }
                ExprKind::Name(_) | ExprKind::Unit | ExprKind::CBit(_) => {}
                ExprKind::Not(input) => stack.push(Node::Expr(input)),
                ExprKind::Tuple(a, b) | ExprKind::And(a, b) | ExprKind::Xor(a, b) => {
                    stack.push(Node::Expr(a));
                    stack.push(Node::Expr(b));
                }
                ExprKind::Call {
                    callee,
                    static_args,
                    args,
                } => {
                    names.push(callee);
                    for op in static_args {
                        operations::called_static_names(op, &mut names);
                    }
                    stack.extend(args.iter().map(Node::Expr));
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.extend([
                        Node::Expr(condition),
                        Node::Block(then_branch),
                        Node::Block(else_branch),
                    ]);
                }
                ExprKind::CoherentLift { input, basis, .. } => {
                    stack.extend([Node::Expr(input), Node::Basis(basis)]);
                }
                ExprKind::WithComputed {
                    source,
                    function,
                    body,
                    ..
                } => {
                    names.push(function);
                    stack.extend([Node::Expr(source), Node::Block(body)]);
                }
                ExprKind::CertifiedComputed {
                    source,
                    function,
                    logical,
                    body,
                    ..
                } => {
                    names.extend([function, logical]);
                    stack.extend([Node::Expr(source), Node::Block(body)]);
                }
            },
            Node::Basis(expr) => match &expr.kind {
                BasisExprKind::Call { callee, args } => {
                    names.push(callee);
                    stack.extend(args.iter().map(Node::Basis));
                }
                BasisExprKind::Tuple(a, b)
                | BasisExprKind::Xor(a, b)
                | BasisExprKind::And(a, b) => {
                    stack.extend([Node::Basis(a), Node::Basis(b)]);
                }
                BasisExprKind::Not(a) => stack.push(Node::Basis(a)),
                _ => {}
            },
        }
    }
    names
}

/// Load and check every declaration, lower `main::main`, then independently
/// verify the generated IR. Public, mutable AST/import records are not trusted
/// inputs to this API; compilation always starts from the source root.
pub fn compile_project(root: &Path) -> Result<VerifiedProgram, CompileError> {
    Ok(process_project(root, true)?.expect("required entry was compiled"))
}

/// Check every declaration in a source root, including library roots with no
/// entry function. Quantum function bodies are independently IR verified.
pub fn check_project(root: &Path) -> Result<(), CompileError> {
    process_project(root, false).map(|_| ())
}

fn process_project(
    root: &Path,
    require_entry: bool,
) -> Result<Option<VerifiedProgram>, CompileError> {
    let project = Project::load_detailed(root).map_err(|failure| {
        let (line, column) = failure.coordinates.unwrap_or((1, 1));
        CompileError {
            code: ErrorCode::Project,
            path: failure.error.path,
            span: failure.error.span,
            line,
            column,
            message: failure.error.message,
        }
    })?;
    process_loaded_project(root, &project, require_entry)
}

/// Check source and IR with structured parse/load categories and optional locations.
/// The existing `check_project` error API remains unchanged.
pub fn check_project_diagnostic(root: &Path) -> Result<(), Diagnostic> {
    process_project_diagnostic(root, false).map(|_| ())
}

/// Compile through the same source and independent IR checks as `compile_project`,
/// retaining structured diagnostics without interpreting human-readable messages.
pub fn compile_project_diagnostic(root: &Path) -> Result<VerifiedProgram, Diagnostic> {
    Ok(process_project_diagnostic(root, true)?.expect("required entry was compiled"))
}

fn process_project_diagnostic(
    root: &Path,
    require_entry: bool,
) -> Result<Option<VerifiedProgram>, Diagnostic> {
    let project = Project::load_detailed(root).map_err(|failure| failure.into_diagnostic())?;
    process_loaded_project(root, &project, require_entry).map_err(Diagnostic::from_compile)
}

fn process_loaded_project(
    root: &Path,
    project: &Project,
    require_entry: bool,
) -> Result<Option<VerifiedProgram>, CompileError> {
    let declarations = project
        .modules
        .iter()
        .flat_map(|(module, source)| {
            source
                .ast
                .decls
                .iter()
                .map(move |decl| ((module.clone(), decl.name.text.clone()), decl))
        })
        .collect();
    let mut compiler = Compiler {
        project,
        declarations,
        basis: BTreeMap::new(),
        checked: BTreeMap::new(),
        function_evidence: BTreeMap::new(),
        meanings: BTreeMap::new(),
        providers: BTreeMap::new(),
        instances: vec![],
        work: 0,
    };
    let order = compiler.order()?;
    let entry = ("main".to_owned(), "main".to_owned());
    if let Some(decl) = compiler.declarations.get(&entry).copied() {
        let (_, result) = compiler.signature(&entry)?;
        if decl.kind != FnKind::Observe
            || !decl.params.is_empty()
            || !decl.static_params.is_empty()
            || !result.classical()
        {
            return Err(compiler.error(
                "main",
                decl.span,
                ErrorCode::InvalidEntry,
                "main must be observe fn main() with a classical result",
            ));
        }
    } else if require_entry {
        return Err(CompileError {
            code: ErrorCode::InvalidEntry,
            path: root.join("main.qli"),
            span: Span::default(),
            line: 1,
            column: 1,
            message: "expected observe fn main() with a classical result".to_owned(),
        });
    }
    // All basis functions precede their callers; ordinary functions may only
    // invoke them through a coherent lift or with_computed predicate.
    for key in &order {
        if compiler.declarations[key].kind == FnKind::Basis {
            let function = compiler.compile_basis(key)?;
            compiler.basis.insert(key.clone(), function);
        }
    }
    for key in &order {
        if compiler.declarations[key].kind == FnKind::Meaning {
            compiler.compile_meaning(key)?;
        }
    }
    let mut main = None;
    for key in &order {
        if !compiler.declarations[key].static_params.is_empty() {
            let bindings = compiler.abstract_bindings(key)?;
            lower::check_generic(&mut compiler, key, bindings)?;
        } else if !matches!(
            compiler.declarations[key].kind,
            FnKind::Basis | FnKind::Meaning
        ) {
            let program = lower::lower_function(&mut compiler, key)?;
            if *key == entry {
                main = Some(program.clone());
            }
            compiler.checked.insert(key.clone(), program);
        }
    }
    Ok(main)
}
