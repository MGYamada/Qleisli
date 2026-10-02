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
use super::project::{ImportOrigin, Project, SourcePolicy};
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
    Tuple(Vec<Ty>),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Preserve exact arity and nesting, including Unit. Iterative rendering
        // also keeps error reporting independent of the Rust call-stack depth.
        enum Part<'a> {
            Type(&'a Ty),
            Text(&'static str),
        }
        let mut pending = vec![Part::Type(self)];
        while let Some(part) = pending.pop() {
            match part {
                Part::Text(text) => f.write_str(text)?,
                Part::Type(ty) => match ty {
                    Ty::Unit => f.write_str("Unit")?,
                    Ty::Bit => f.write_str("Bit")?,
                    Ty::CBit => f.write_str("CBit")?,
                    Ty::Q(inner) => {
                        f.write_str("Q<")?;
                        pending.extend([Part::Text(">"), Part::Type(inner)]);
                    }
                    Ty::Pair(a, b) => {
                        f.write_str("(")?;
                        pending.extend([
                            Part::Text(")"),
                            Part::Type(b),
                            Part::Text(","),
                            Part::Type(a),
                        ]);
                    }
                    Ty::Tuple(fields) => {
                        f.write_str("(")?;
                        pending.push(Part::Text(")"));
                        for (index, field) in fields.iter().enumerate().rev() {
                            pending.push(Part::Type(field));
                            if index > 0 {
                                pending.push(Part::Text(","));
                            }
                        }
                    }
                },
            }
        }
        Ok(())
    }
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
                Self::Tuple(fields) => {
                    pending.extend(fields.iter().map(|field| (field, depth + 1)))
                }
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
            Self::Tuple(fields) => fields
                .iter()
                .try_fold(0, |bits, field| Some(bits + field.basis_bits()?)),
            _ => None,
        }
    }

    fn classical(&self) -> bool {
        match self {
            Self::Unit | Self::CBit => true,
            Self::Pair(a, b) => a.classical() && b.classical(),
            Self::Tuple(fields) => fields.iter().all(Self::classical),
            _ => false,
        }
    }

    fn pair(a: Self, b: Self) -> Self {
        Self::Pair(Box::new(a), Box::new(b))
    }

    fn tuple(mut fields: Vec<Self>) -> Self {
        if fields.len() == 2 {
            let b = fields.pop().expect("second field");
            Self::pair(fields.pop().expect("first field"), b)
        } else {
            Self::Tuple(fields)
        }
    }

    fn fields(&self) -> Option<Vec<&Self>> {
        match self {
            Self::Pair(a, b) => Some(vec![a, b]),
            Self::Tuple(fields) => Some(fields.iter().collect()),
            _ => None,
        }
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
    // One immutable, full-project snapshot. It is copied only when evidence is
    // first needed and charged before allocation. Individual receipts share it.
    function_sources: Option<Arc<Vec<(String, String)>>>,
    meanings: BTreeMap<Key, operations::DeclaredMeaning>,
    providers: BTreeMap<(Key, Option<Key>), operations::Operation>,
    instances: Vec<(Key, Vec<operations::Operation>)>,
    work: usize,
    checking: Option<Key>,
    exact_work: crate::contract::exact::Budget,
    closed_meanings: BTreeMap<Key, crate::contract::exact::Matrix>,
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
            let (line, column) = coordinates(&self.project.modules[module].source, span);
            let (owner, location, context) = match &self.checking {
                Some(key) => (
                    key.0.as_str(),
                    self.declarations[key].span,
                    format!(" while checking {}::{}", key.0, key.1),
                ),
                None => (module, span, String::new()),
            };
            return Err(self.error(
                owner,
                location,
                ErrorCode::Limit,
                format!(
                    "source expansion exceeds the project-wide work limit of {MAX_WORK}{context}; \
                    {} units used, {amount} requested at {module}:{line}:{column}; \
                    each declaration is checked and each call is expanded separately",
                    self.work
                ),
            ));
        }
        self.work += amount;
        Ok(())
    }

    fn retained_sources(
        &mut self,
        module: &str,
        span: Span,
    ) -> Result<Arc<Vec<(String, String)>>, CompileError> {
        if let Some(sources) = &self.function_sources {
            return Ok(Arc::clone(sources));
        }
        // The evidence checker independently checks the metadata again. This
        // preflight bounds the vector and source/path storage before cloning.
        if self.project.modules.len() > crate::contract::function::MAX_FUNCTION_SOURCES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "function identity exceeds its metadata profile (at most 128 source modules)",
            ));
        }
        let source_bytes = total_size(self.project.modules.values().map(|s| s.source.len()));
        self.charge(module, span, source_bytes).map_err(|mut error| {
            error.message.push_str(&format!(
                "; retaining {source_bytes} source bytes in the shared project snapshot (all loaded modules, comments and bundled std); this snapshot is charged once across static providers and function contracts"
            ));
            error
        })?;
        // Loaded module paths are already bounded by the filesystem. Keep the
        // evidence profile explicit here instead of cloning arbitrary strings.
        if self
            .project
            .modules
            .keys()
            .any(|name| name.len() > crate::contract::function::MAX_IDENTITY_NAME_BYTES)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "function source identity paths exceed their 4096-byte limit",
            ));
        }
        let retained_bytes =
            source_bytes.saturating_add(total_size(self.project.modules.keys().map(String::len)));
        if retained_bytes > crate::contract::function::MAX_FUNCTION_SOURCE_BYTES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "shared function source snapshot exceeds 1 MiB including module names",
            ));
        }
        let sources = Arc::new(
            self.project
                .modules
                .iter()
                .map(|(name, source)| (name.clone(), source.source.clone()))
                .collect(),
        );
        self.function_sources = Some(Arc::clone(&sources));
        Ok(sources)
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
            TypeKind::Tuple(fields) => Ty::tuple(
                fields
                    .iter()
                    .map(|field| self.ty(module, field, basis_only))
                    .collect::<Result<_, _>>()?,
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
                    PatternKind::Tuple(fields) => pending.extend(fields.iter().rev()),
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
            for name in called_names(decl)
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

fn called_names(decl: &Decl) -> Vec<&Ident> {
    fn pattern_names(pattern: &Pattern) -> Vec<&Ident> {
        let mut pending = vec![pattern];
        let mut names = Vec::new();
        while let Some(pattern) = pending.pop() {
            match &pattern.kind {
                PatternKind::Name(name) => names.push(name),
                PatternKind::Tuple(fields) => pending.extend(fields),
                PatternKind::Wildcard => {}
            }
        }
        names
    }
    enum Node<'a> {
        Expr(&'a Expr),
        Basis(&'a BasisExpr),
        Block(&'a Block, Vec<&'a Ident>),
        Bind(Vec<&'a Ident>),
        Unbind(Vec<&'a Ident>),
        Names(Vec<&'a Ident>),
    }
    if let FnBody::Meaning { function, .. } = &decl.body {
        return vec![function];
    }
    let mut locals = BTreeMap::<&str, usize>::new();
    for name in decl.params.iter().flat_map(|p| pattern_names(&p.pattern)) {
        *locals.entry(&name.text).or_default() += 1;
    }
    let mut stack = vec![match &decl.body {
        FnBody::Meaning { .. } => unreachable!(),
        FnBody::Basis(expr) => Node::Basis(expr),
        FnBody::Quantum(block) => Node::Block(block, vec![]),
    }];
    let mut names = Vec::new();
    while let Some(node) = stack.pop() {
        match node {
            Node::Names(calls) => names.extend(
                calls
                    .into_iter()
                    .filter(|n| !locals.contains_key(n.text.as_str())),
            ),
            Node::Bind(bindings) => {
                for name in bindings {
                    *locals.entry(&name.text).or_default() += 1;
                }
            }
            Node::Unbind(bindings) => {
                for name in bindings {
                    let count = locals
                        .get_mut(name.text.as_str())
                        .expect("entered lexical binding");
                    *count -= 1;
                    if *count == 0 {
                        locals.remove(name.text.as_str());
                    }
                }
            }
            Node::Block(block, extra) => {
                let mut bindings = extra.clone();
                for name in extra {
                    *locals.entry(&name.text).or_default() += 1;
                }
                bindings.extend(block.statements.iter().flat_map(|stmt| match &stmt.kind {
                    StmtKind::Let { pattern, .. } => pattern_names(pattern),
                    StmtKind::Expr(_) => vec![],
                }));
                stack.push(Node::Unbind(bindings));
                stack.push(Node::Expr(&block.result));
                // Initializers precede their bindings. Spent local names keep
                // shadowing declarations until the containing scope ends.
                for stmt in block.statements.iter().rev() {
                    match &stmt.kind {
                        StmtKind::Let { pattern, value } => {
                            stack.push(Node::Bind(pattern_names(pattern)));
                            stack.push(Node::Expr(value));
                        }
                        StmtKind::Expr(expr) => stack.push(Node::Expr(expr)),
                    }
                }
            }
            Node::Expr(expr) => match &expr.kind {
                ExprKind::ApplyContract {
                    implementation,
                    specification,
                    input,
                } => {
                    stack.push(Node::Expr(input));
                    stack.push(Node::Names(vec![implementation, specification]));
                }
                ExprKind::Adjoint { function, input }
                | ExprKind::RepeatStatic {
                    function, input, ..
                } => {
                    stack.push(Node::Expr(input));
                    stack.push(Node::Names(vec![function]));
                }
                ExprKind::QuantumIf {
                    control,
                    target,
                    zero,
                    one,
                } => {
                    stack.extend([Node::Expr(control), Node::Expr(target)]);
                    stack.push(Node::Names(vec![zero, one]));
                }
                ExprKind::Name(_) | ExprKind::Unit | ExprKind::CBit(_) => {}
                ExprKind::Not(input) => stack.push(Node::Expr(input)),
                ExprKind::Tuple(fields) => stack.extend(fields.iter().map(Node::Expr)),
                ExprKind::And(a, b) | ExprKind::Xor(a, b) => {
                    stack.push(Node::Expr(a));
                    stack.push(Node::Expr(b));
                }
                ExprKind::Call {
                    callee,
                    static_args,
                    args,
                } => {
                    let mut calls = vec![callee];
                    for op in static_args {
                        operations::called_static_names(op, &mut calls);
                    }
                    stack.extend(args.iter().map(Node::Expr));
                    stack.push(Node::Names(calls));
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.extend([
                        Node::Expr(condition),
                        Node::Block(then_branch, vec![]),
                        Node::Block(else_branch, vec![]),
                    ]);
                }
                ExprKind::CoherentLift {
                    input,
                    basis,
                    binder,
                } => {
                    let bindings = pattern_names(binder);
                    stack.extend([
                        Node::Unbind(bindings.clone()),
                        Node::Basis(basis),
                        Node::Bind(bindings),
                        Node::Expr(input),
                    ]);
                }
                ExprKind::WithComputed {
                    source,
                    function,
                    binder,
                    body,
                } => {
                    stack.extend([Node::Block(body, vec![binder]), Node::Expr(source)]);
                    stack.push(Node::Names(vec![function]));
                }
                ExprKind::CertifiedComputed {
                    source,
                    function,
                    logical,
                    data_binder,
                    ancilla_binder,
                    body,
                } => {
                    stack.extend([
                        Node::Block(body, vec![data_binder, ancilla_binder]),
                        Node::Expr(source),
                    ]);
                    stack.push(Node::Names(vec![function, logical]));
                }
            },
            Node::Basis(expr) => match &expr.kind {
                BasisExprKind::Call { callee, args } => {
                    stack.extend(args.iter().map(Node::Basis));
                    stack.push(Node::Names(vec![callee]));
                }
                BasisExprKind::Tuple(fields) => stack.extend(fields.iter().map(Node::Basis)),
                BasisExprKind::Xor(a, b) | BasisExprKind::And(a, b) => {
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
    process_project_with_policy(root, require_entry, SourcePolicy::Legacy)
}

/// Check all declarations using an explicit pre-tokenization byte policy.
pub fn check_project_with_policy(root: &Path, policy: SourcePolicy) -> Result<(), Diagnostic> {
    process_project_with_policy(root, false, policy).map(|_| ())
}

/// Compile and independently verify using an explicit source-loading policy.
pub fn compile_project_with_policy(
    root: &Path,
    policy: SourcePolicy,
) -> Result<VerifiedProgram, Diagnostic> {
    Ok(process_project_with_policy(root, true, policy)?.expect("required entry was compiled"))
}

fn process_project_with_policy(
    root: &Path,
    require_entry: bool,
    policy: SourcePolicy,
) -> Result<Option<VerifiedProgram>, Diagnostic> {
    let project = Project::load_detailed_with_policy(root, policy)
        .map_err(|failure| failure.into_diagnostic())?;
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
        function_sources: None,
        meanings: BTreeMap::new(),
        providers: BTreeMap::new(),
        instances: vec![],
        work: 0,
        checking: None,
        exact_work: crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        closed_meanings: BTreeMap::new(),
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
        compiler.checking = Some(key.clone());
        if compiler.declarations[key].kind == FnKind::Basis {
            let function = compiler.compile_basis(key)?;
            compiler.basis.insert(key.clone(), function);
        }
    }
    for key in &order {
        compiler.checking = Some(key.clone());
        if compiler.declarations[key].kind == FnKind::Meaning {
            compiler.compile_meaning(key)?;
        }
    }
    let mut main = None;
    for key in &order {
        compiler.checking = Some(key.clone());
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

#[cfg(test)]
mod snapshot_tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    fn project(extra: usize) -> Project {
        let mut modules = BTreeMap::new();
        for (name, bytes) in [("main", 100_000), ("unrelated", extra)] {
            let source = "p".repeat(bytes);
            modules.insert(
                name.into(),
                SourceModule {
                    name: name.into(),
                    path: PathBuf::from(format!("{name}.qli")),
                    source,
                    ast: Module {
                        uses: vec![],
                        decls: vec![],
                        span: Span::default(),
                    },
                    imports: BTreeMap::new(),
                    origin: ModuleOrigin::Local,
                },
            );
        }
        Project {
            root: PathBuf::new(),
            modules,
        }
    }

    fn compiler(project: &Project) -> Compiler<'_> {
        Compiler {
            project,
            declarations: BTreeMap::new(),
            basis: BTreeMap::new(),
            checked: BTreeMap::new(),
            function_evidence: BTreeMap::new(),
            function_sources: None,
            meanings: BTreeMap::new(),
            providers: BTreeMap::new(),
            instances: vec![],
            work: 0,
            checking: None,
            exact_work: crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
            closed_meanings: BTreeMap::new(),
        }
    }

    #[test]
    fn ir_narrowing_reports_overflow_at_the_original_source_without_wrapping() {
        let project = project(0);
        let compiler = compiler(&project);
        let span = Span::new(10, 12);
        for field in ["input width", "split width", "phase label"] {
            for value in [256, 65536, usize::MAX] {
                let error = compiler.narrow_u8("main", span, value, field).unwrap_err();
                assert_eq!(error.code, ErrorCode::Limit);
                assert_eq!(error.span, span);
                assert!(error.message.contains(field));
                assert!(error.message.contains(&value.to_string()));
                assert!(error.message.contains("no truncation"));
            }
            for value in [0, 12, 255] {
                assert_eq!(
                    usize::from(compiler.narrow_u8("main", span, value, field).unwrap()),
                    value
                );
            }
        }
    }

    #[test]
    fn retained_source_bytes_are_charged_once_for_256_receipts() {
        for extra in [0, 25_003] {
            let project = project(extra);
            let mut compiler = compiler(&project);
            let snapshots = (0..256)
                .map(|_| compiler.retained_sources("main", Span::default()).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(compiler.work, 100_000 + extra);
            assert_eq!(
                total_size(snapshots[0].iter().map(|(_, source)| source.len())),
                100_000 + extra
            );
            assert!(
                snapshots
                    .iter()
                    .all(|source| Arc::ptr_eq(source, &snapshots[0]))
            );
            assert_ne!(
                snapshots[0][0].1.as_ptr(),
                project.modules["main"].source.as_ptr()
            );
        }
    }

    #[test]
    fn the_initial_snapshot_is_bounded_before_copying_even_at_the_work_boundary() {
        let project = project(25_003);
        let mut accepted = compiler(&project);
        accepted.work = MAX_WORK - 125_003;
        accepted.retained_sources("main", Span::default()).unwrap();
        assert_eq!(accepted.work, MAX_WORK);
        accepted.retained_sources("main", Span::default()).unwrap();
        assert_eq!(accepted.work, MAX_WORK);
        let mut rejected = compiler(&project);
        rejected.work = MAX_WORK - 125_002;
        let error = rejected
            .retained_sources("main", Span::default())
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::Limit);
        assert!(error.message.contains("charged once"));
        assert!(rejected.function_sources.is_none());
    }

    #[test]
    fn metadata_storage_limits_are_preflighted_before_the_source_copy() {
        for (count, name_bytes, extra_source) in [(127, 4, 0), (1, 4097, 0), (126, 4096, 440_000)] {
            let mut project = project(extra_source);
            let mut empty = project.modules["main"].clone();
            empty.source.clear();
            for index in 0..count {
                let name = format!("{index:03}{}", "n".repeat(name_bytes - 3));
                project.modules.insert(name, empty.clone());
            }
            let mut compiler = compiler(&project);
            assert_eq!(
                compiler
                    .retained_sources("main", Span::default())
                    .unwrap_err()
                    .code,
                ErrorCode::Limit
            );
            assert!(compiler.function_sources.is_none());
        }
    }
}
