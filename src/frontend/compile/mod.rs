//! Checked lowering of the finite source subset to independently verified IR.

mod basis;
mod circuit;
mod lower;
mod operations;
mod profile;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::ast::*;
use super::check::{self, Interface, SourceError, SourceLimits, StaticKind};
use super::diagnostic::{Diagnostic, coordinates};
use super::project::{Project, SourcePolicy};
use super::resolve::{DefId, Resolution, Target};
use crate::AcceptedProgram;

const MAX_BITS: usize = 12;
const MAX_WORK: usize = 1_000_000;
const MAX_DEPTH: usize = 64;
const MAX_TREE_NODES: usize = 4096;
const MAX_TREE_DEPTH: usize = 64;
type Key = DefId;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum MeaningCacheKey {
    Declaration(Key),
    Sealed(String, String),
}

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

use super::types::{Kind, Stage, TreeSize};
// Registers are outside the finite source profile; the uninhabited size keeps
// that restriction explicit while using the same exact type tree as sized code.
type Ty = super::types::Type<std::convert::Infallible>;

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display(Stage::Basis).fmt(f)
    }
}
impl Ty {
    fn basis_bits(&self) -> Option<usize> {
        match &self.kind {
            Kind::Unit => Some(0),
            Kind::Bit => Some(1),
            Kind::Bits(n) => match *n {},
            Kind::Tuple(fields) => fields
                .iter()
                .try_fold(0, |bits, field| Some(bits + field.basis_bits()?)),
            Kind::Q(_) | Kind::Parameter(_) => None,
        }
    }
    fn classical(&self) -> bool {
        !self.linear()
    }
    fn runtime(&self) -> super::types::DisplayType<'_, std::convert::Infallible> {
        self.display(Stage::Runtime)
    }
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

use super::resolve::locals::{BinderKey, Forest, OccurrencesForest, ResolvedUse};

struct Compiler<'a> {
    kernel: crate::interchange::native::Kernel,
    project: &'a Project,
    resolution: Resolution,
    locals: Forest<'a>,
    interfaces: BTreeMap<Key, Interface>,
    declarations: BTreeMap<Key, &'a Decl>,
    basis: BTreeMap<Key, BasisFunction>,
    checked: BTreeMap<Key, AcceptedProgram>,
    effects: BTreeMap<Key, super::effects::FunctionEffect>,
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
    closed_meanings: BTreeMap<MeaningCacheKey, crate::contract::exact::Matrix>,
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
        let mut work = self.work;
        self.charge_at(&mut work, module, span, amount)?;
        self.work = work;
        Ok(())
    }

    fn charge_at(
        &self,
        work: &mut usize,
        module: &str,
        span: Span,
        amount: usize,
    ) -> Result<(), CompileError> {
        if amount > MAX_WORK.saturating_sub(*work) {
            let (line, column) = coordinates(&self.project.modules[module].source, span);
            let (owner, location, context) = match &self.checking {
                Some(key) => (
                    self.resolution.declaration(*key).name.0.as_str(),
                    self.declarations[key].span,
                    format!(" while checking {}", self.resolution.path(*key)),
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
                    *work
                ),
            ));
        }
        *work += amount;
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
        match self.locals.usage(name).target {
            ResolvedUse::Global(Target::Declaration(id)) => Ok(Callee::User(id)),
            ResolvedUse::Global(Target::Primitive(id)) => {
                Ok(Callee::Sealed(id.module.into(), id.name.into()))
            }
            ResolvedUse::Local(_) | ResolvedUse::Unresolved => Err(self.error(
                module,
                name.span,
                ErrorCode::UnknownName,
                format!(
                    "unknown function `{}`; standard operations require an explicit import",
                    name.text
                ),
            )),
        }
    }

    fn signature(&mut self, key: &Key) -> Result<(Vec<Ty>, Ty), CompileError> {
        let decl = self.declarations[key];
        let interface = &self.interfaces[key];
        let module = self.resolution.declaration(*key).name.0.clone();
        assert_eq!(interface.module, module, "checked interface module");
        assert_eq!(interface.kind, decl.kind, "checked declaration kind");
        assert_eq!(
            interface.params.len(),
            decl.params.len(),
            "checked parameter count"
        );
        assert_eq!(
            interface.statics.len(),
            decl.static_params.len(),
            "checked static count"
        );
        let stage = if decl.kind == FnKind::Classical {
            Stage::Basis
        } else {
            Stage::Runtime
        };
        let mut work = self.work;
        let result: Result<(Vec<Ty>, Ty), CompileError> = (|| {
            let mut params = Vec::new();
            for (ordinal, parameter) in decl.params.iter().enumerate() {
                params.push(finite_type(
                    self,
                    &mut work,
                    &module,
                    &parameter.ty,
                    &interface.params[ordinal],
                    stage,
                )?);
            }
            let result = finite_type(
                self,
                &mut work,
                &module,
                &decl.return_type,
                &interface.result,
                stage,
            )?;
            Ok((params, result))
        })();
        self.work = work;
        let (params, result) = result?;
        if decl.kind == FnKind::Classical {
            for (ordinal, parameter) in decl.params.iter().enumerate() {
                if !matches!(parameter.pattern.kind, PatternKind::Name(_)) {
                    // Concrete labels still use the actual finite pattern/label binder.
                    self.bind_basis_pattern(&module, &parameter.pattern, &params[ordinal], 0)?;
                }
            }
        }
        Ok((params, result))
    }
}

/// Convert the checked symbolic interface, preserving its exact type tree.
/// Original types supply locations only; this is finite eligibility and copying,
/// never another source type/ownership judgment.
fn finite_type(
    compiler: &Compiler<'_>,
    work: &mut usize,
    module: &str,
    original: &Type,
    checked: &check::Ty,
    stage: Stage,
) -> Result<Ty, CompileError> {
    let charge_node = |work: &mut usize| {
        let size = checked.tree_size();
        if size.nodes > MAX_TREE_NODES || size.depth > MAX_TREE_DEPTH {
            return Err(compiler.error(module, original.span, ErrorCode::Limit, format!("internal value or type exceeds the initial {MAX_TREE_NODES}-node / {MAX_TREE_DEPTH}-level limit")));
        }
        compiler.charge_at(work, module, original.span, size.nodes)
    };
    let ty = match (&original.kind, &checked.kind) {
        (TypeKind::Unit, Kind::Unit) => {
            charge_node(work)?;
            Ty::unit()
        }
        (TypeKind::Bit, Kind::Bit) => {
            charge_node(work)?;
            Ty::bit()
        }
        (TypeKind::Q(original), Kind::Q(checked)) => {
            let basis = finite_type(compiler, work, module, original, checked, Stage::Basis)?;
            charge_node(work)?;
            Ty::quantum(basis)
        }
        (TypeKind::Tuple(original), Kind::Tuple(checked)) => {
            assert_eq!(original.len(), checked.len(), "checked tuple arity");
            let mut fields = Vec::new();
            for (ordinal, field) in original.iter().enumerate() {
                fields.push(finite_type(
                    compiler,
                    work,
                    module,
                    field,
                    &checked[ordinal],
                    stage,
                )?);
            }
            charge_node(work)?;
            Ty::tuple(fields)
        }
        (_, Kind::Bits(_)) => {
            return Err(compiler.error(
                module,
                original.span,
                ErrorCode::Unsupported,
                "register types are outside the finite lowering profile",
            ));
        }
        (_, Kind::Parameter(_)) => {
            return Err(compiler.error(
                module,
                original.span,
                ErrorCode::Unsupported,
                "named Basis types are outside the finite lowering profile",
            ));
        }
        _ => unreachable!("finite source and checked interface constructors differ"),
    };
    if stage == Stage::Basis && ty.basis_bits().is_some_and(|bits| bits > MAX_BITS) {
        return Err(compiler.error(
            module,
            original.span,
            ErrorCode::Limit,
            "basis type exceeds the initial 12-bit limit",
        ));
    }
    Ok(ty)
}

/// Load and check every declaration, lower `main::main`, then independently
/// verify the generated IR. Public, mutable AST/import records are not trusted
/// inputs to this API; compilation always starts from the source root.
pub fn compile_project(root: &Path) -> Result<AcceptedProgram, CompileError> {
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
) -> Result<Option<AcceptedProgram>, CompileError> {
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
pub fn compile_project_diagnostic(root: &Path) -> Result<AcceptedProgram, Diagnostic> {
    Ok(process_project_diagnostic(root, true)?.expect("required entry was compiled"))
}

fn process_project_diagnostic(
    root: &Path,
    require_entry: bool,
) -> Result<Option<AcceptedProgram>, Diagnostic> {
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
) -> Result<AcceptedProgram, Diagnostic> {
    Ok(process_project_with_policy(root, true, policy)?.expect("required entry was compiled"))
}

/// Check all executable declarations through the selected native kernel,
/// including libraries without `main`.
/// Symbolic generic declarations remain frontend checks until instantiated.
pub fn check_project_with_kernel(
    root: &Path,
    policy: SourcePolicy,
    kernel: &crate::interchange::native::Kernel,
) -> Result<(), Diagnostic> {
    process_project_with_kernel(root, false, policy, kernel).map(|_| ())
}

/// Compile after native checking every concrete function, including unused
/// declarations. The returned entry is reconstructed from accepted bytes.
pub fn compile_project_with_kernel(
    root: &Path,
    policy: SourcePolicy,
    kernel: &crate::interchange::native::Kernel,
) -> Result<AcceptedProgram, Diagnostic> {
    Ok(process_project_with_kernel(root, true, policy, kernel)?
        .expect("required entry was compiled"))
}

fn process_project_with_kernel(
    root: &Path,
    require_entry: bool,
    policy: SourcePolicy,
    kernel: &crate::interchange::native::Kernel,
) -> Result<Option<AcceptedProgram>, Diagnostic> {
    let project = Project::load_detailed_with_policy(root, policy)
        .map_err(|failure| failure.into_diagnostic())?;
    process_loaded_project_with_kernel(root, &project, require_entry, Some(kernel))
        .map_err(Diagnostic::from_compile)
}

fn process_project_with_policy(
    root: &Path,
    require_entry: bool,
    policy: SourcePolicy,
) -> Result<Option<AcceptedProgram>, Diagnostic> {
    let project = Project::load_detailed_with_policy(root, policy)
        .map_err(|failure| failure.into_diagnostic())?;
    process_loaded_project(root, &project, require_entry).map_err(Diagnostic::from_compile)
}

impl super::project::QrateSource {
    /// Selected native checking retains this qrate's pinned source identity.
    pub fn check_with_kernel(
        &self,
        policy: SourcePolicy,
        kernel: &crate::interchange::native::Kernel,
    ) -> Result<(), Diagnostic> {
        let project = self.load_with_policy(policy)?;
        process_loaded_project_with_kernel(self.path(), &project, false, Some(kernel))
            .map(|_| ())
            .map_err(Diagnostic::from_compile)
    }

    /// Compile every concrete declaration through the selected kernel.
    pub fn compile_with_kernel(
        &self,
        policy: SourcePolicy,
        kernel: &crate::interchange::native::Kernel,
    ) -> Result<AcceptedProgram, Diagnostic> {
        let project = self.load_with_policy(policy)?;
        Ok(
            process_loaded_project_with_kernel(self.path(), &project, true, Some(kernel))
                .map_err(Diagnostic::from_compile)?
                .expect("required entry was compiled"),
        )
    }

    /// Check every declaration in the selected qrate, retaining its root identity.
    pub fn check_with_policy(&self, policy: SourcePolicy) -> Result<(), Diagnostic> {
        let project = self.load_with_policy(policy)?;
        process_loaded_project(self.path(), &project, false)
            .map(|_| ())
            .map_err(Diagnostic::from_compile)
    }

    /// Compile the selected qrate through the same independent source/IR checks.
    pub fn compile_with_policy(&self, policy: SourcePolicy) -> Result<AcceptedProgram, Diagnostic> {
        let project = self.load_with_policy(policy)?;
        Ok(process_loaded_project(self.path(), &project, true)
            .map_err(Diagnostic::from_compile)?
            .expect("required entry was compiled"))
    }
}

fn process_loaded_project(
    root: &Path,
    project: &Project,
    require_entry: bool,
) -> Result<Option<AcceptedProgram>, CompileError> {
    process_loaded_project_with_kernel(root, project, require_entry, None)
}

fn process_loaded_project_with_kernel(
    root: &Path,
    project: &Project,
    require_entry: bool,
    kernel: Option<&crate::interchange::native::Kernel>,
) -> Result<Option<AcceptedProgram>, CompileError> {
    process_loaded_project_details(root, project, require_entry, kernel).map(|result| result.entry)
}

struct ProjectResult {
    entry: Option<AcceptedProgram>,
    effects: BTreeMap<String, super::effects::FunctionEffect>,
}

/// Immutable interface facts bound to the source collection actually checked.
/// These facts grant no execution handle, arbitrary Meaning or access evidence.
#[derive(Clone, Debug)]
pub struct ProjectEffects {
    project: Project,
    functions: BTreeMap<String, super::effects::FunctionEffect>,
}

impl ProjectEffects {
    pub fn function_effect(&self, path: &str) -> Option<super::effects::FunctionEffect> {
        self.functions.get(path).copied()
    }

    /// Render the retained checked source, including inferred effects on
    /// ordinary functions. Basis/Meaning declarations have no quantum fact.
    pub fn documentation(&self, module: &str) -> Option<Result<String, super::parser::ParseError>> {
        self.project.modules.get(module).map(|source| {
            super::documentation::render_checked_markdown(&source.source, |name| {
                self.function_effect(&format!("{module}::{name}"))
            })
        })
    }
}

/// Derive interface facts through the same whole-project source checks and
/// native verification of concrete functions as `check_project_with_kernel`.
/// Generic body facts remain conditional on their checked source premises.
pub fn project_effects_with_kernel(
    root: &Path,
    policy: SourcePolicy,
    kernel: &crate::interchange::native::Kernel,
) -> Result<ProjectEffects, Diagnostic> {
    let project = Project::load_detailed_with_policy(root, policy)
        .map_err(|failure| failure.into_diagnostic())?;
    let result = process_loaded_project_details(root, &project, false, Some(kernel))
        .map_err(Diagnostic::from_compile)?;
    Ok(ProjectEffects {
        project,
        functions: result.effects,
    })
}

fn process_loaded_project_details(
    root: &Path,
    project: &Project,
    require_entry: bool,
    kernel: Option<&crate::interchange::native::Kernel>,
) -> Result<ProjectResult, CompileError> {
    // Public Project fields can be mutated by a caller. Reconstruct the entire
    // original judgment and occurrence association on every operation.
    let (source, occurrences) = check::program_with(
        project
            .modules
            .iter()
            .map(|(name, module)| (name.as_str(), &module.ast))
            .collect(),
        SourceLimits::finite(),
        |resolution, _, _, _, indices, budget| {
            let mut occurrences = OccurrencesForest::default();
            for (id, index) in indices {
                let declaration = resolution.declaration(*id);
                let span =
                    project.modules[&declaration.name.0].ast.decls[declaration.ast_index].span;
                occurrences.insert_budgeted(
                    index.take_occurrences(),
                    span,
                    &mut |span, cells| budget.charge(span, cells),
                )?;
            }
            Ok(occurrences)
        },
    )
    .map_err(|error| source_error(project, root, error))?;
    let order = source.dependency_order;
    let resolution = source.resolution;
    let declarations: BTreeMap<_, _> = resolution
        .declarations()
        .map(|(id, declaration)| {
            (
                id,
                &project.modules[&declaration.name.0].ast.decls[declaration.ast_index],
            )
        })
        .collect();
    // These are located pending concrete obligations, not proof discharges.
    // Concrete lowering/evidence gates remain responsible when instantiated.
    let _obligations = source.obligations;
    for (id, declaration) in &declarations {
        if declaration.kind == FnKind::Static {
            continue;
        }
        if let Err((span, message)) = profile::check(declaration) {
            return Err(source_error(
                project,
                root,
                SourceError::new("unsupported", span, message)
                    .in_module(&resolution.declaration(*id).name.0),
            ));
        }
    }
    let locals = Forest::from_occurrences(source.lexical, occurrences);
    let kernel = kernel
        .cloned()
        .map(Ok)
        .unwrap_or_else(crate::interchange::native::Kernel::selected)
        .map_err(|error| CompileError {
            code: ErrorCode::Project,
            path: root.into(),
            span: Span::default(),
            line: 1,
            column: 1,
            message: error.to_string(),
        })?;
    let mut compiler = Compiler {
        kernel,
        project,
        resolution,
        declarations,
        locals,
        interfaces: source.interfaces,
        basis: BTreeMap::new(),
        checked: BTreeMap::new(),
        effects: source.effects,
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
    let entry = compiler.resolution.qualified("main::main").ok();
    if let Some((entry, decl)) =
        entry.and_then(|id| compiler.declarations.get(&id).map(|decl| (id, *decl)))
    {
        if decl.kind == FnKind::Static {
            return Err(compiler.error(
                "main",
                decl.span,
                ErrorCode::InvalidEntry,
                "a static Nat helper cannot be a runtime entry",
            ));
        }
        let (_, result) = compiler.signature(&entry)?;
        if matches!(decl.kind, FnKind::Classical | FnKind::Meaning)
            || !decl.params.is_empty()
            || !decl.static_params.is_empty()
            || !result.classical()
        {
            return Err(compiler.error(
                "main",
                decl.span,
                ErrorCode::InvalidEntry,
                "main must be an ordinary fn main() with a closed classical result",
            ));
        }
    } else if require_entry {
        return Err(CompileError {
            code: ErrorCode::InvalidEntry,
            path: root.join("main.qli"),
            span: Span::default(),
            line: 1,
            column: 1,
            message: "expected ordinary fn main() with a closed classical result".to_owned(),
        });
    }
    // Prepare finite descriptions for static/coherent obligations. Ordinary
    // calls lower the original classical body; they do not execute this table.
    for key in &order {
        compiler.checking = Some(*key);
        if compiler.declarations[key].kind == FnKind::Classical {
            let function = compiler.compile_basis(key)?;
            compiler.basis.insert(*key, function);
        }
    }
    for key in &order {
        compiler.checking = Some(*key);
        if compiler.declarations[key].kind == FnKind::Meaning {
            compiler.compile_meaning(key)?;
        }
    }
    let mut main = None;
    for key in &order {
        compiler.checking = Some(*key);
        if compiler.declarations[key].static_params.is_empty()
            && !matches!(
                compiler.declarations[key].kind,
                FnKind::Classical | FnKind::Meaning
            )
        {
            let program = lower::lower_function(&mut compiler, key)?;
            if Some(*key) == entry {
                main = Some(program.clone());
            }
            compiler.checked.insert(*key, program);
        }
    }
    let effects = compiler
        .effects
        .iter()
        .map(|(key, fact)| (compiler.resolution.path(*key), *fact))
        .collect();
    Ok(ProjectResult {
        entry: main,
        effects,
    })
}

fn source_error(project: &Project, root: &Path, error: SourceError) -> CompileError {
    let code = match error.code {
        "name" => ErrorCode::UnknownName,
        "cycle" => ErrorCode::RecursiveCall,
        "arity" | "static-arity" => ErrorCode::Arity,
        "type" | "size" | "static" | "shadow" => ErrorCode::TypeMismatch,
        "ownership" | "binding" => ErrorCode::Ownership,
        "effect" => ErrorCode::Effect,
        "access" => ErrorCode::Capability,
        "contract" => ErrorCode::Contract,
        "unsupported" => ErrorCode::Unsupported,
        "limit" => ErrorCode::Limit,
        _ => ErrorCode::Project,
    };
    let (path, line, column) = error
        .module
        .as_ref()
        .and_then(|module| project.modules.get(module))
        .map_or_else(
            || (root.to_path_buf(), 1, 1),
            |module| {
                let (line, column) = coordinates(&module.source, error.span);
                (module.path.clone(), line, column)
            },
        );
    CompileError {
        code,
        path,
        span: error.span,
        line,
        column,
        message: error.message,
    }
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
            kernel: crate::interchange::native::Kernel::selected().expect("explicit test kernel"),
            project,
            resolution: project
                .resolution()
                .map_err(|failure| failure.into_diagnostic())
                .expect("valid test project"),
            declarations: BTreeMap::new(),
            locals: Forest::default(),
            interfaces: BTreeMap::new(),
            basis: BTreeMap::new(),
            checked: BTreeMap::new(),
            effects: BTreeMap::new(),
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
    fn constructed_ordinary_parameter_patterns_use_runtime_binding_rules() {
        let source = "unitary fn keep(u: Unit) -> Unit { () }";
        for kind in [PatternKind::Tuple(vec![]), PatternKind::Wildcard] {
            let mut project = project(0);
            let module = project.modules.get_mut("main").unwrap();
            module.source = source.into();
            module.ast = crate::frontend::parser::parse_module(source).unwrap();
            let parameter = &mut module.ast.decls[0].params[0];
            parameter.pattern.kind = kind;
            assert!(
                process_loaded_project(Path::new("main.qli"), &project, false)
                    .expect("constructed ordinary Unit pattern")
                    .is_none()
            );
        }
        let source = "unitary fn keep(q: Q<Bit>) -> Q<Bit> { q }";
        for (kind, code, message) in [
            (
                PatternKind::Tuple(vec![]),
                ErrorCode::TypeMismatch,
                "empty pattern requires ordinary Unit",
            ),
            (
                PatternKind::Wildcard,
                ErrorCode::Ownership,
                "wildcard would discard quantum ownership",
            ),
        ] {
            let mut project = project(0);
            let module = project.modules.get_mut("main").unwrap();
            module.source = source.into();
            module.ast = crate::frontend::parser::parse_module(source).unwrap();
            let parameter = &mut module.ast.decls[0].params[0];
            let span = parameter.pattern.span;
            parameter.pattern.kind = kind;
            let error = process_loaded_project(Path::new("main.qli"), &project, false)
                .expect_err("constructed pattern cannot eliminate a quantum owner");
            assert_eq!(error.code, code);
            assert_eq!(error.path, PathBuf::from("main.qli"));
            assert_eq!(error.span, span);
            assert!(error.message.contains(message));
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
