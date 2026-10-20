//! Source checking, explicit specialization, and lowering to independently verified IR.
//!
//! Project inputs and explicit module collections share the common frontend.
//! `ParsedProgram` retains checked source preparation; instantiation and proposal
//! generation do not by themselves confer independent native acceptance.
//!
//! The former `frontend::sized` namespace was removed in 0.3.0. Import its
//! preparation and binding types from this module instead.
//! ```compile_fail,E0432
//! use qleisli::frontend::sized::ParsedProgram;
//! ```

mod basis;
mod calls;
mod circuit;
mod dormant;
mod instances;
mod interfaces;
mod lower;
mod naturals;
mod operations;
mod profile;
mod report;
mod sources;
mod types;

use types::finite_type;

pub use report::ProjectCheckReport;

pub use super::specialize::{
    BasisBinding, CheckedSourceMeanings, ElaboratedProgram, Error, FramePort, HierarchyEligibility,
    HierarchyProposal, InitializationMove, Instantiation, OperationBinding, ParsedProgram,
    PreparationValidation, QpeBindingProposal, RawSourceProposal, SourceDefinition, SourceEvent,
    SourceMeaningCheck, SourceOperation, SourceStep, SourceType, SourceValue, Span,
};

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::ast::*;
use super::check::{self, Interface, SourceError, SourceLimits, StaticKind};
use super::diagnostic::{Diagnostic, coordinates};
use super::project::{Project, SourcePolicy};
use super::resolve::{DefId, PrimitiveId, Target};
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
    Primitive(PrimitiveId, String),
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

impl ErrorCode {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            ErrorCode::Project => "project",
            ErrorCode::UnknownName => "unknown_name",
            ErrorCode::RecursiveCall => "recursive_call",
            ErrorCode::TypeMismatch => "type_mismatch",
            ErrorCode::Arity => "arity",
            ErrorCode::Ownership => "ownership",
            ErrorCode::Effect => "effect",
            ErrorCode::InvalidEntry => "invalid_entry",
            ErrorCode::Unsupported => "unsupported",
            ErrorCode::Limit => "limit",
            ErrorCode::InvalidIr => "invalid_ir",
            ErrorCode::Capability => "capability",
            ErrorCode::Contract => "contract",
        }
    }
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
// Closed sizes retain their exact unsigned representation. Admitting a source
// form remains the profile's separate decision; this representation grants no
// generic binding, conversion or accepted handle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RegisterWidthError {
    Unresolved,
    Capacity,
}

trait FiniteRegisterSize {
    fn finite_width(&self) -> Result<u32, RegisterWidthError>;
}
impl FiniteRegisterSize for u32 {
    fn finite_width(&self) -> Result<u32, RegisterWidthError> {
        Ok(*self)
    }
}
impl FiniteRegisterSize for check::Linear {
    fn finite_width(&self) -> Result<u32, RegisterWidthError> {
        if !self.terms.is_empty() {
            return Err(RegisterWidthError::Unresolved);
        }
        u32::try_from(self.constant).map_err(|_| RegisterWidthError::Capacity)
    }
}

type Ty = super::types::Type<u32>;

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
            Kind::Bits(size) => usize::try_from(*size).ok(),
            Kind::Tuple(fields) => fields
                .iter()
                .try_fold(0usize, |bits, field| bits.checked_add(field.basis_bits()?)),
            Kind::Q(_) | Kind::Parameter(_) => None,
        }
    }
    fn classical(&self) -> bool {
        !self.linear()
    }
    fn runtime(&self) -> super::types::DisplayType<'_, u32> {
        self.display(Stage::Runtime)
    }
    fn empty_bits() -> Self {
        Self::bits(0)
    }
}

fn total_size(sizes: impl IntoIterator<Item = usize>) -> usize {
    sizes.into_iter().fold(0, usize::saturating_add)
}

#[derive(Clone, Debug)]
enum Callee {
    User(Key),
    Primitive(PrimitiveId),
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

use super::resolve::locals::{BinderKey, Forest, Lookup, OccurrencesForest, ResolvedUse};

struct Compiler<'a> {
    kernel: crate::interchange::native::Kernel,
    project: &'a Project,
    // Retain the single complete judgment over the original loaded source.
    // Adapters borrow its facts; they neither reconstruct nor replace them.
    source: check::CheckedProgram,
    // Captured and independently associated while the original indices and
    // checked helper templates were still available. Normalized sizes cannot
    // replace the ordinary Nat expression's intermediate checks.
    interface_naturals: BTreeMap<Key, check::plans::InterfaceNaturals>,
    locals: Forest<'a>,
    declarations: BTreeMap<Key, &'a Decl>,
    basis: BTreeMap<Key, BasisFunction>,
    checked: BTreeMap<Key, AcceptedProgram>,
    // Private to this immutable loaded project. Dependencies are checked once
    // in topological order and never replaced, so a cache hit keeps its exact
    // source/raw binding without rescanning those frozen snapshots.
    function_evidence: BTreeMap<(Key, Key), Arc<crate::contract::FunctionEvidence>>,
    instrument_evidence: BTreeMap<
        (Key, Key, Key, Option<usize>),
        Arc<crate::contract::instrument::InstrumentEvidence>,
    >,
    // Complete original module rows are copied once; each receipt retains its
    // relevant lexical/evidence closure without coupling unrelated modules.
    source_rows: BTreeMap<String, Arc<(String, String)>>,
    source_sets: BTreeMap<Vec<String>, crate::contract::function::SourceRows>,
    pure_equations: Vec<Arc<crate::interchange::pure_leaf::SourcePureEquation>>,
    computed_normalizations: Vec<Arc<crate::interchange::finite_leaf::SourceUnitaryEquation>>,
    meanings: BTreeMap<Key, operations::DeclaredMeaning>,
    providers: BTreeMap<(Key, Option<Key>, crate::ir::Effect), operations::CachedProvider>,
    instances: Vec<instances::Record>,
    concrete_context: instances::Context,
    work: usize,
    checking: Option<Key>,
    exact_work: crate::contract::exact::Budget,
    closed_meanings: BTreeMap<MeaningCacheKey, crate::contract::exact::Matrix>,
}

impl<'a> Compiler<'a> {
    // Occurrence addresses borrow the original AST while authoritative tables
    // remain in the checked collection. The view copies no table or map.
    fn locals(&self) -> Lookup<'_, 'a> {
        self.locals.lookup(&self.source.lexical)
    }

    // Source eligibility follows the original caller and callee modules, even
    // when concrete lowering later inlines the callee's checked body.
    fn effect_in_module(&self, module: &str, callee: Key) -> Option<crate::ir::Effect> {
        let module = self.source.resolution.module(module)?;
        super::effects::effect_at(
            &self.source.resolution,
            &self.source.effects,
            super::effects::EffectContext::Module(module),
            callee,
        )
    }

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
            message: super::diagnostic::without_repeated_category(code.as_str(), message.into()),
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
                    self.source.resolution.declaration(*key).name.0.as_str(),
                    self.declarations[key].span,
                    format!(" while checking {}", self.source.resolution.path(*key)),
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
        match self.locals().usage(name).target {
            ResolvedUse::Global(Target::Declaration(id)) => Ok(Callee::User(id)),
            ResolvedUse::Global(Target::Primitive(id)) => Ok(Callee::Primitive(id)),
            ResolvedUse::Local(_) | ResolvedUse::Unresolved => Err(self.error(
                module,
                name.span,
                ErrorCode::UnknownName,
                format!(
                    "unknown function `{}`; ordinary library definitions require an explicit import",
                    name.text
                ),
            )),
        }
    }

    fn signature(&mut self, key: &Key) -> Result<(Vec<Ty>, Ty), CompileError> {
        let decl = self.declarations[key];
        let module = self.dormant_module(*key, decl.span)?;
        let interface = &self.source.interfaces[key];
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
        // Meaning has a distinct domain/result contract, not a runtime
        // interface. Runtime and classical functions share exact closure with
        // selected-source lowering. The existing whole-source finite profile
        // still refuses Basis/Nat declarations before this adapter is reached.
        let closed = if decl.kind == FnKind::Meaning {
            None
        } else {
            Some(self.closed_runtime_interface(*key, decl.span)?)
        };
        let interface = &self.source.interfaces[key];
        let mut work = self.work;
        let result: Result<(Vec<Ty>, Ty), CompileError> = (|| {
            let mut params = Vec::new();
            for (ordinal, parameter) in decl.params.iter().enumerate() {
                let ty = match &closed {
                    Some(closed) => finite_type(
                        self,
                        &mut work,
                        &module,
                        &parameter.ty,
                        &closed.parameters[ordinal],
                        stage,
                    ),
                    None => finite_type(
                        self,
                        &mut work,
                        &module,
                        &parameter.ty,
                        &interface.params[ordinal],
                        stage,
                    ),
                }?;
                params.push(ty);
            }
            let result = match &closed {
                Some(closed) => finite_type(
                    self,
                    &mut work,
                    &module,
                    &decl.return_type,
                    &closed.result,
                    stage,
                ),
                None => finite_type(
                    self,
                    &mut work,
                    &module,
                    &decl.return_type,
                    &interface.result,
                    stage,
                ),
            }?;
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

    /// Close only already eligible finite runtime interfaces. Empty Basis/Nat
    /// maps are deliberate: this connection enables no generic instance. All
    /// Op ports are closed too, but actual provider/access/Meaning obligations
    /// remain at their existing concrete evidence gates.
    fn closed_runtime_interface(
        &mut self,
        definition: Key,
        span: Span,
    ) -> Result<super::closed::ClosedInterface, CompileError> {
        let module = self.dormant_module(definition, span)?;
        let current = self
            .concrete_context
            .current
            .as_ref()
            .filter(|instance| instance.definition == definition);
        let mut work = self.work;
        let bindings: Result<_, CompileError> = (|| {
            if let Some(instance) = current {
                for (key, ty) in &instance.interface.bases {
                    self.charge_at(
                        &mut work,
                        &module,
                        span,
                        key.name.len() + ty.tree_size().nodes + 1,
                    )?;
                }
                for key in instance.interface.naturals.keys() {
                    self.charge_at(&mut work, &module, span, key.name.len() + 2)?;
                }
                Ok((
                    instance.interface.bases.clone(),
                    instance.interface.naturals.clone(),
                ))
            } else {
                Ok((BTreeMap::new(), BTreeMap::new()))
            }
        })();
        self.work = work;
        let (bases, naturals) = bindings?;
        self.close_instance_interface(definition, bases, naturals, span)
    }

    fn close_instance_interface(
        &mut self,
        definition: Key,
        bases: BTreeMap<BinderKey, super::types::Type<u32>>,
        naturals: BTreeMap<BinderKey, u32>,
        span: Span,
    ) -> Result<super::closed::ClosedInterface, CompileError> {
        let module = self.dormant_module(definition, span)?;
        let work = std::cell::Cell::new(self.work);
        let charge_error = std::cell::RefCell::new(None);
        let result = (|| {
            // Preserve the adapter's original located work-limit diagnostic.
            // A temporary source error only propagates out of the closer; the
            // actual CompileError is returned below, without conversion loss.
            let charge = |span, cells| {
                let mut used = work.get();
                let result = self
                    .charge_at(&mut used, &module, span, cells)
                    .map_err(|error| {
                        *charge_error.borrow_mut() = Some(error);
                        SourceError::new("limit", span, "finite closed-interface work limit")
                    });
                work.set(used);
                result
            };
            for basis in bases.values() {
                types::closed_basis_capacity(basis, span, &mut |span, cells| charge(span, cells))?;
            }
            let checked = super::closed::CheckedInterface::original(
                &self.source,
                definition,
                span,
                &mut |span, cells| charge(span, cells),
            )?;
            let substitution = super::closed::ClosedSubstitution::binders_budgeted(
                checked,
                bases,
                naturals,
                "finite runtime function",
                &mut |span, cells| charge(span, cells),
            )?;
            // The bounded finite copy below still applies this adapter's exact
            // constructor, tree and width limits. This callback grants nothing.
            super::closed::close_interface_budgeted(
                substitution,
                "finite runtime function",
                &mut |span, cells| charge(span, cells),
                |ty, span| types::closed_capacity(ty, span, &mut |span, cells| charge(span, cells)),
            )
        })();
        self.work = work.get();
        if let Some(error) = charge_error.into_inner() {
            return Err(error);
        }
        let closed = result.map_err(|error| {
            source_error(self.project, &self.project.root, error.in_module(&module))
        })?;
        self.validate_interface_naturals(definition, &closed, span)?;
        Ok(closed)
    }
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
    check_project_report_with_kernel(root, policy, kernel).map(|_| ())
}

/// Check every declaration and report the actual successful native decisions.
/// An independent contract for one body does not establish entry or whole-source
/// preservation. Libraries without an entry remain valid check inputs.
pub fn check_project_report_with_kernel(
    root: &Path,
    policy: SourcePolicy,
    kernel: &crate::interchange::native::Kernel,
) -> Result<ProjectCheckReport, Diagnostic> {
    let project = Project::load_detailed_with_policy(root, policy)
        .map_err(|failure| failure.into_diagnostic())?;
    let (kernel, decisions) = kernel.recording();
    let result = process_loaded_project_details(root, &project, false, Some(&kernel))
        .map_err(Diagnostic::from_compile)?;
    Ok(ProjectCheckReport::new(result, decisions.summary()))
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
        self.check_report_with_kernel(policy, kernel).map(|_| ())
    }

    /// Retain the selected directory identity and report successful native checks.
    /// The report is diagnostic metadata, not a reusable acceptance handle.
    pub fn check_report_with_kernel(
        &self,
        policy: SourcePolicy,
        kernel: &crate::interchange::native::Kernel,
    ) -> Result<ProjectCheckReport, Diagnostic> {
        let project = self.load_with_policy(policy)?;
        let (kernel, decisions) = kernel.recording();
        let result = process_loaded_project_details(self.path(), &project, false, Some(&kernel))
            .map_err(Diagnostic::from_compile)?;
        Ok(ProjectCheckReport::new(result, decisions.summary()))
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

impl Project {
    /// Check the already captured source and edition without rereading its files.
    pub fn check_report_with_kernel(
        &self,
        kernel: &crate::interchange::native::Kernel,
    ) -> Result<ProjectCheckReport, Diagnostic> {
        let (kernel, decisions) = kernel.recording();
        let result = process_loaded_project_details(&self.root, self, false, Some(&kernel))
            .map_err(Diagnostic::from_compile)?;
        Ok(ProjectCheckReport::new(result, decisions.summary()))
    }

    /// Compile the same captured project with its explicit, matching native context.
    pub fn compile_with_kernel(
        &self,
        kernel: &crate::interchange::native::Kernel,
    ) -> Result<AcceptedProgram, Diagnostic> {
        Ok(
            process_loaded_project_with_kernel(&self.root, self, true, Some(kernel))
                .map_err(Diagnostic::from_compile)?
                .expect("required entry was compiled"),
        )
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
    concrete_local_roots: usize,
    concrete_bundled_roots: usize,
}

/// Immutable interface facts bound to the source collection actually checked.
/// These facts grant no execution handle, arbitrary Meaning or access evidence.
#[derive(Clone, Debug)]
pub struct ProjectEffects {
    project: Project,
    functions: BTreeMap<String, super::effects::FunctionEffect>,
}

impl ProjectEffects {
    /// Inspect the implementation principal, assertion and checked public effect.
    /// `inferred()` is diagnostic/internal information; external callers and
    /// host-selected public providers must use `public_effect()` for eligibility.
    /// These facts confer no native acceptance, Meaning or operation access.
    pub fn function_effect(&self, path: &str) -> Option<super::effects::FunctionEffect> {
        self.functions.get(path).copied()
    }

    /// The checked exported effect of a public source declaration.
    /// Private, absent or unchecked declarations have no exported contract.
    /// This grants no inverse/control, Meaning, cleanup or execution evidence.
    pub fn public_function_effect(&self, path: &str) -> Option<crate::ir::Effect> {
        self.function_effect(path)?.public_effect()
    }

    /// Render checked public contracts and private inferred diagnostics from
    /// the retained source. Basis/Meaning declarations have no quantum fact.
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

struct PreparedSource<'ast> {
    checked: check::CheckedProgram,
    occurrences: OccurrencesForest<'ast>,
    interface_naturals: BTreeMap<Key, check::plans::InterfaceNaturals>,
}

fn prepare_original_source<'ast>(
    root: &Path,
    project: &'ast Project,
) -> Result<PreparedSource<'ast>, CompileError> {
    project.validate_edition_context().map_err(|failure| {
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
    // Public Project fields can be mutated by a caller. Reconstruct the entire
    // original judgment and occurrence association on every operation.
    let (source, (occurrences, interface_naturals)) = check::program_with(
        project
            .modules
            .iter()
            .map(|(name, module)| (name.as_str(), &module.ast))
            .collect(),
        SourceLimits::finite(),
        |resolution, interfaces, helpers, _, _, indices, budget| {
            let mut interface_naturals = BTreeMap::new();
            // Capture every signature before moving any original occurrence
            // association out of the common checker's indices.
            budget.charge(Span::default(), interfaces.len())?;
            for id in interfaces.keys() {
                let record = resolution.declaration(*id);
                let declaration = &project.modules[&record.name.0].ast.decls[record.ast_index];
                let original = check::plans::capture_interface_naturals_budgeted(
                    check::plans::InterfaceNaturalContext {
                        owner: *id,
                        declaration,
                        resolution,
                        interfaces,
                        indices,
                        helpers,
                        budget,
                    },
                )
                .map_err(|error| error.in_module(&record.name.0))?;
                budget
                    .charge(declaration.span, 1)
                    .map_err(|error| error.in_module(&record.name.0))?;
                interface_naturals.insert(*id, original);
            }
            let mut occurrences = OccurrencesForest::default();
            for (id, index) in indices {
                let declaration = resolution.declaration(*id);
                let span =
                    project.modules[&declaration.name.0].ast.decls[declaration.ast_index].span;
                occurrences
                    .insert_budgeted(index.take_occurrences(), span, &mut |span, cells| {
                        budget.charge(span, cells)
                    })
                    .map_err(|error| error.in_module(&declaration.name.0))?;
            }
            Ok((occurrences, interface_naturals))
        },
    )
    .map_err(|error| source_error(project, root, error))?;
    Ok(PreparedSource {
        checked: source,
        occurrences,
        interface_naturals,
    })
}

fn process_loaded_project_details(
    root: &Path,
    project: &Project,
    require_entry: bool,
    kernel: Option<&crate::interchange::native::Kernel>,
) -> Result<ProjectResult, CompileError> {
    let PreparedSource {
        checked: source,
        occurrences,
        interface_naturals,
    } = prepare_original_source(root, project)?;
    let declarations: BTreeMap<_, _> = source
        .resolution
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
    for (id, declaration) in &declarations {
        if declaration.kind == FnKind::Static {
            continue;
        }
        if let Err((span, message)) = profile::check(declaration, &source.interfaces[id]) {
            return Err(source_error(
                project,
                root,
                SourceError::new("unsupported", span, message)
                    .in_module(&source.resolution.declaration(*id).name.0),
            ));
        }
    }
    let locals = Forest::from_occurrences(occurrences);
    let kernel = kernel
        .cloned()
        .map(Ok)
        .unwrap_or_else(|| crate::interchange::native::Kernel::selected(project.edition()))
        .map_err(|error| CompileError {
            code: ErrorCode::Project,
            path: root.into(),
            span: Span::default(),
            line: 1,
            column: 1,
            message: error.to_string(),
        })?;
    if kernel.edition() != project.edition() {
        return Err(CompileError {
            code: ErrorCode::Project,
            path: root.into(),
            span: Span::default(),
            line: 1,
            column: 1,
            message: "selected native kernel edition differs from the captured project edition"
                .into(),
        });
    }
    let mut compiler = Compiler {
        kernel,
        project,
        source,
        interface_naturals,
        declarations,
        locals,
        basis: BTreeMap::new(),
        checked: BTreeMap::new(),
        function_evidence: BTreeMap::new(),
        instrument_evidence: BTreeMap::new(),
        source_rows: BTreeMap::new(),
        source_sets: BTreeMap::new(),
        pure_equations: Vec::new(),
        computed_normalizations: Vec::new(),
        meanings: BTreeMap::new(),
        providers: BTreeMap::new(),
        instances: vec![],
        concrete_context: instances::Context::default(),
        work: 0,
        checking: None,
        exact_work: crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        closed_meanings: BTreeMap::new(),
    };
    let entry = compiler.source.resolution.qualified("main::main").ok();
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
    for ordinal in 0..compiler.source.dependency_order.len() {
        // Copy only this immutable identity before mutably lowering its body;
        // the original dependency collection stays in its checked owner.
        let key = compiler.source.dependency_order[ordinal];
        compiler.checking = Some(key);
        if compiler.declarations[&key].kind == FnKind::Classical {
            let function = compiler.compile_basis(&key)?;
            compiler.basis.insert(key, function);
        }
    }
    let mut main = None;
    for ordinal in 0..compiler.source.dependency_order.len() {
        let key = compiler.source.dependency_order[ordinal];
        compiler.checking = Some(key);
        if compiler.declarations[&key].kind == FnKind::Meaning {
            compiler.compile_meaning(&key)?;
            continue;
        }
        if compiler.declarations[&key].static_params.is_empty()
            && !matches!(
                compiler.declarations[&key].kind,
                FnKind::Classical | FnKind::Meaning
            )
        {
            let program = lower::lower_function(&mut compiler, &key)?;
            if Some(key) == entry {
                main = Some(program.clone());
            }
            compiler.checked.insert(key, program);
        }
    }
    compiler.check_dormant_operations()?;
    compiler.check_dormant_controls()?;
    // FunctionEquality names closed pairs even inside an unused generic body
    // or a zero-count branch. Source checking is not their semantic discharge.
    for ordinal in 0..compiler.source.obligations.len() {
        let obligation = &compiler.source.obligations[ordinal];
        if let check::ObligationKind::FunctionEquality {
            implementation,
            specification,
        } = &obligation.kind
        {
            // Read the existing record; do not clone or remove its obligation.
            let (definition, span, implementation, specification) = (
                obligation.definition,
                obligation.span,
                *implementation,
                *specification,
            );
            compiler.checking = Some(definition);
            let module = compiler
                .source
                .resolution
                .declaration(definition)
                .name
                .0
                .clone();
            if compiler.effect_in_module(&module, implementation)
                == Some(crate::ir::Effect::Observe)
            {
                compiler.instrument_contract_evidence(
                    &module,
                    span,
                    implementation,
                    specification,
                )?;
            } else {
                compiler.function_contract_evidence(
                    &module,
                    span,
                    implementation,
                    specification,
                )?;
            }
        }
    }
    let effects = compiler
        .source
        .effects
        .iter()
        .map(|(key, fact)| (compiler.source.resolution.path(*key), *fact))
        .collect();
    compiler.charge("main", Span::default(), compiler.instrument_evidence.len())?;
    let (concrete_local_roots, concrete_bundled_roots) =
        compiler
            .checked
            .keys()
            .fold((0, 0), |(local, bundled), key| {
                let module = &compiler.source.resolution.declaration(*key).name.0;
                match project.modules[module].origin {
                    super::project::ModuleOrigin::Local => (local + 1, bundled),
                    super::project::ModuleOrigin::Bundled => (local, bundled + 1),
                }
            });
    Ok(ProjectResult {
        entry: main.map(|program| {
            program
                .retain_instruments(compiler.instrument_evidence.into_values().collect())
                .retain_pure_equations(compiler.pure_equations)
                .retain_computed_normalizations(compiler.computed_normalizations)
        }),
        effects,
        concrete_local_roots,
        concrete_bundled_roots,
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
mod empty_register_tests {
    use super::*;
    use crate::contract::instrument::ResultAtom;

    #[test]
    fn complete_instrument_result_schema_preserves_empty_register_unit_and_owner_tags() {
        let input = Ty::quantum(Ty::empty_bits());
        let output = Ty::tuple(vec![
            Ty::empty_bits(),
            Ty::bit(),
            Ty::unit(),
            Ty::quantum(Ty::empty_bits()),
        ]);
        let signature = crate::frontend::instrument::signature(
            &[input],
            &output,
            |_| Some(0),
            &mut crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap();
        assert_eq!(signature.input, crate::contract::BasisType::Bits(0));
        assert_eq!(
            signature.result,
            vec![
                ResultAtom::Tuple(4),
                ResultAtom::Bits(0),
                ResultAtom::Bit,
                ResultAtom::Unit,
                ResultAtom::Quantum(crate::contract::BasisType::Bits(0)),
            ]
        );
        assert_ne!(Ty::empty_bits(), Ty::unit());
        assert_eq!(Ty::empty_bits().to_string(), "Bits<0>");
        assert_eq!(
            Ty::quantum(Ty::empty_bits()).runtime().to_string(),
            "Q<Bits<0>>"
        );
    }
}

#[cfg(test)]
mod snapshot_tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    #[test]
    fn source_preparation_rejects_a_substituted_edition_inventory() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/bell");
        let original = Project::load_with_policy(&root, SourcePolicy::default()).unwrap();
        assert!(prepare_original_source(&root, &original).is_ok());
        for mutation in 0..5 {
            let mut changed = original.clone();
            match mutation {
                0 => changed.root.push("replacement"),
                1 => changed
                    .modules
                    .get_mut("main")
                    .unwrap()
                    .path
                    .push("replacement"),
                2 => changed.modules.get_mut("main").unwrap().origin = ModuleOrigin::Bundled,
                3 => {
                    changed.modules.remove("std::transform");
                }
                _ => {
                    changed
                        .modules
                        .insert("other".into(), changed.modules["main"].clone());
                }
            }
            let failure = prepare_original_source(&root, &changed).err().unwrap();
            assert_eq!(failure.code, ErrorCode::Project);
            assert!(
                failure.message.contains("captured edition context"),
                "{failure}"
            );
            assert!(changed.module_manifest("main").is_none() || mutation >= 3);
        }
    }

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
                        no_implicit_prelude: false,
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
            edition_context: crate::frontend::project::ProjectEdition::Explicit(
                crate::edition::Edition::E2026,
            ),
            root: PathBuf::new(),
            modules,
        }
    }

    pub(super) fn compiler(project: &Project) -> Compiler<'_> {
        let PreparedSource {
            checked: source,
            occurrences,
            interface_naturals,
        } = prepare_original_source(Path::new("main.qli"), project)
            .expect("valid test source judgment");
        let declarations = source
            .resolution
            .declarations()
            .map(|(id, record)| {
                (
                    id,
                    &project.modules[&record.name.0].ast.decls[record.ast_index],
                )
            })
            .collect();
        Compiler {
            kernel: crate::interchange::native::Kernel::selected(crate::edition::Edition::E2026)
                .expect("explicit test kernel"),
            project,
            source,
            interface_naturals,
            declarations,
            locals: Forest::from_occurrences(occurrences),
            basis: BTreeMap::new(),
            checked: BTreeMap::new(),
            function_evidence: BTreeMap::new(),
            instrument_evidence: BTreeMap::new(),
            source_rows: BTreeMap::new(),
            source_sets: BTreeMap::new(),
            pure_equations: Vec::new(),
            computed_normalizations: Vec::new(),
            meanings: BTreeMap::new(),
            providers: BTreeMap::new(),
            instances: vec![],
            concrete_context: instances::Context::default(),
            work: 0,
            checking: None,
            exact_work: crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
            closed_meanings: BTreeMap::new(),
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
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

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
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

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn retained_source_bytes_are_charged_once_for_256_receipts() {
        for extra in [0, 25_003] {
            let project = project(extra);
            let mut compiler = compiler(&project);
            let mut snapshots = Vec::new();
            for i in 0..256 {
                // Different closures share the exact same interned main record.
                let names = if i % 2 == 0 {
                    vec!["main".to_owned()]
                } else {
                    vec!["main".to_owned(), "unrelated".to_owned()]
                };
                snapshots.push(
                    compiler
                        .retain_source_modules("main", Span::default(), names)
                        .unwrap(),
                );
            }
            assert!(
                compiler.work < 150_000 + extra,
                "source bytes were recopied across closures"
            );
            assert!(
                snapshots
                    .iter()
                    .all(|source| Arc::ptr_eq(&source[0], &snapshots[0][0]))
            );
            assert_eq!(snapshots[0][0].1, project.modules["main"].source);
            assert_ne!(
                snapshots[0][0].1.as_ptr(),
                project.modules["main"].source.as_ptr()
            );
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn the_initial_snapshot_is_bounded_before_copying_even_at_the_work_boundary() {
        let project = project(25_003);
        let names = vec!["main".to_owned(), "unrelated".to_owned()];
        let mut probe = compiler(&project);
        probe
            .retain_source_modules("main", Span::default(), names.clone())
            .unwrap();
        let required = probe.work;
        let mut accepted = compiler(&project);
        accepted.work = MAX_WORK - required;
        accepted
            .retain_source_modules("main", Span::default(), names.clone())
            .unwrap();
        assert_eq!(accepted.work, MAX_WORK);
        let mut rejected = compiler(&project);
        rejected.work = MAX_WORK - required + 1;
        let error = rejected
            .retain_source_modules("main", Span::default(), names)
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::Limit);
        assert!(error.message.contains("charged once"));
        assert!(rejected.source_rows.is_empty());
        assert!(rejected.source_sets.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn metadata_storage_limits_are_preflighted_before_the_source_copy() {
        // Keep each constructed source collection within the common judgment's
        // work budget, while exceeding the independent snapshot metadata bound.
        // In the aggregate case, names alone must not exhaust source checking
        // before retained_sources can exercise its complete-byte preflight.
        for (count, name_bytes, extra_source, message) in [
            (127, 4, 0, "at most 128 source modules"),
            (1, 4097, 0, "4096-byte limit"),
            (100, 4096, 550_000, "1 MiB including module names"),
        ] {
            let mut project = project(extra_source);
            let mut empty = project.modules["main"].clone();
            empty.source.clear();
            for index in 0..count {
                let name = format!("{index:03}{}", "n".repeat(name_bytes - 3));
                project.modules.insert(name, empty.clone());
            }
            let mut compiler = compiler(&project);
            let names = project.modules.keys().cloned().collect();
            let error = compiler
                .retain_source_modules("main", Span::default(), names)
                .unwrap_err();
            assert_eq!(error.code, ErrorCode::Limit);
            assert!(error.message.contains(message), "{error}");
            assert!(compiler.source_rows.is_empty());
            assert!(compiler.source_sets.is_empty());
        }
    }
}
