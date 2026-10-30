//! Internal preparation for bounded source specialization and lowering.
//!
//! Parsing, resolution, types, ownership and effects belong to the common
//! frontend. This adapter consumes that judgment, closes supplied bindings and
//! projects bodies into its concrete lowering representation. Preparation values
//! are not verified IR, execution handles or evidence of source preservation.

mod ast;
mod basis_binding;
mod bindings;
mod elaborate;
mod lower;
mod meaning;
mod primitive;
mod projection;
mod qpe;
mod raw;

pub(in crate::frontend) use basis_binding::carrier_description_budgeted;

use super::resolve::{DefId, Failure, FailureKind};
use super::source::{self, ParsePolicy, Source, SourceCollection};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

pub use super::ast::Span;
pub use super::error::Error;
pub use elaborate::{
    ElaboratedProgram, HierarchyEligibility, SourceDefinition, SourceOperation, SourceStep,
    SourceType, SourceValue,
};
pub use lower::{
    FramePort, HierarchyProposal, InitializationMove, PreparationValidation, SourceEvent,
};
pub use raw::{CheckedSourceCarrier, CheckedSourceMeanings, RawSourceProposal, SourceMeaningCheck};

use super::error::Result;
pub use qpe::QpeBindingProposal;
const MAX_MODULES: usize = 64;
const MAX_SOURCE_BYTES: usize = 65_536;
const MAX_TOTAL_BYTES: usize = 1_048_576;

impl From<super::check::SourceError> for Error {
    fn from(error: super::check::SourceError) -> Self {
        Self {
            code: match error.code {
                "binding" | "shadow" => "name",
                "static-arity" => "static",
                code => code,
            },
            module: error.module,
            span: error.span,
            message: error.message,
        }
    }
}

/// An opaque source collection with privately represented syntax and generic
/// preparation checks. Cloning this value does not create checked IR evidence.
#[derive(Clone, Debug)]
pub struct ParsedProgram {
    edition: crate::edition::Edition,
    manifests: Arc<BTreeMap<String, Arc<super::project::EditionManifest>>>,
    sources: Arc<SourceCollection>,
    checked: Arc<super::check::CheckedProgram>,
    // A concrete eligibility result for every original definition. Unsupported
    // siblings retain their identity and checked facts; selecting one reports
    // its actual located lowering restriction.
    projections: Arc<BTreeMap<DefId, Result<Arc<ast::Function>>>>,
    // Original resolved identities and exact trees, not spelling/width keys.
    meaning_targets: Arc<BTreeMap<DefId, meaning::TargetTable>>,
}
impl ParsedProgram {
    pub fn edition(&self) -> crate::edition::Edition {
        self.edition
    }

    /// Exact selecting manifest retained for a local module; in-memory modules
    /// have an explicit API edition instead. Bundled std never selects it.
    pub fn module_manifest(&self, module: &str) -> Option<&super::project::EditionManifest> {
        self.manifests.get(module).map(Arc::as_ref)
    }

    /// Describe one original finite Meaning as an untrusted mathematical target.
    /// This selects no provider, verifies no artifact and grants no execution.
    /// Exact Bits tags are unsupported by the legacy finite signature; they
    /// are never replaced by a same-width Unit, Bit or product.
    pub fn finite_meaning_target(
        &self,
        path: &str,
    ) -> Result<crate::contract::meaning::FiniteMeaning> {
        let id = self.checked.resolution.qualified(path).map_err(|kind| {
            Self::resolution_error(Failure {
                module: String::new(),
                span: Span::default(),
                kind,
            })
        })?;
        let declaration = self.checked.resolution.declaration(id);
        let original = &self
            .sources
            .get(&declaration.name.0)
            .expect("retained source")
            .syntax()
            .decls[declaration.ast_index];
        let target = self.meaning_targets.get(&id).ok_or_else(|| {
            Error::new(
                "meaning",
                original.span,
                "requested definition is not a finite Meaning",
            )
            .in_module(&declaration.name.0)
        })?;
        target
            .finite(original.span)
            .map_err(|e| e.in_module(&declaration.name.0))
    }

    /// Render only this preparation's immutable retained bytes and body facts.
    /// Generic facts remain conditional on checked source premises, not IR evidence.
    pub fn documentation(
        &self,
        module: &str,
    ) -> Option<std::result::Result<String, super::parser::ParseError>> {
        self.sources.get(module).map(|source| {
            super::documentation::render_checked_markdown(source.text(), |name| {
                self.function_effect(&format!("{module}::{name}"))
            })
        })
    }

    /// The retained common source AST. It is untrusted syntax, not checked IR.
    pub fn syntax(&self, module: &str) -> Option<&super::ast::Module> {
        self.sources.get(module).map(Source::syntax)
    }

    /// Parse and check every supplied module, including unused imports and both
    /// arms of static branches. Imports must resolve within this complete map or
    /// to a primitive explicitly specified by this bounded profile.
    pub fn parse(
        edition: crate::edition::Edition,
        sources: BTreeMap<String, String>,
    ) -> Result<Self> {
        // Reject before constructing the path-bearing adapter map. The caller
        // may supply an oversized map; its count must not trigger another one.
        Self::supplied_module_count(sources.len())?;
        Self::parse_inputs(
            edition,
            sources
                .into_iter()
                .map(|(name, text)| (name, (None, text)))
                .collect(),
            BTreeMap::new(),
        )
    }

    fn supplied_module_count(count: usize) -> Result<()> {
        let bundled = source::BundledRegistry::sources().len();
        if count == 0 || count > MAX_MODULES.saturating_sub(bundled) {
            return Err(Error::new(
                "limit",
                Span::default(),
                format!(
                    "provide 1 through {} local modules; {bundled} bundled modules count toward {MAX_MODULES}",
                    MAX_MODULES.saturating_sub(bundled)
                ),
            ));
        }
        Ok(())
    }

    fn bundled_bytes() -> Result<usize> {
        source::BundledRegistry::sources()
            .iter()
            .try_fold(0usize, |used, bundled| {
                used.checked_add(bundled.text().len()).ok_or_else(|| {
                    Error::new(
                        "limit",
                        Span::default(),
                        "bundled source byte count overflow",
                    )
                })
            })
    }

    fn parse_inputs(
        edition: crate::edition::Edition,
        sources: BTreeMap<String, (Option<PathBuf>, String)>,
        manifests: BTreeMap<String, Arc<super::project::EditionManifest>>,
    ) -> Result<Self> {
        Self::supplied_module_count(sources.len())?;
        super::project::check_bundled_manifest().map_err(|e| {
            Error::new(
                e.code,
                e.primary.map_or(Span::default(), |p| p.span),
                e.message,
            )
        })?;
        let mut seen = std::collections::BTreeSet::new();
        let mut total = 0usize;
        for manifest in manifests.values() {
            if manifest.edition() != edition {
                return Err(Error::new(
                    "edition",
                    Span::default(),
                    "mixed captured constitutional editions",
                ));
            }
            if seen.insert(manifest.path()) {
                total = total.checked_add(manifest.source().len()).ok_or_else(|| {
                    Error::new("limit", Span::default(), "manifest byte count overflow")
                })?;
            }
        }
        let mut collection = source::Builder::default();
        for (name, (path, source)) in sources {
            if !valid_module_name(&name) {
                return Err(
                    Error::new("module", Span::default(), "invalid module path").in_module(&name)
                );
            }
            total = total.checked_add(source.len()).ok_or_else(|| {
                Error::new("limit", Span::default(), "source byte count overflow")
            })?;
            if source.len() > MAX_SOURCE_BYTES || total > MAX_TOTAL_BYTES {
                return Err(Error::new(
                    "limit",
                    Span::default(),
                    "source exceeds 64 KiB per module or 1 MiB aggregate",
                )
                .in_module(&name));
            }
            let module = Source::local(name.clone(), path, source, ParsePolicy::ExplicitModules)
                .map_err(Self::collection_error)?;
            collection.insert(module).map_err(|duplicate| {
                Error::new(
                    "module",
                    Span::default(),
                    format!("duplicate module {duplicate}"),
                )
                .in_module(&name)
            })?;
        }
        for bundled in source::BundledRegistry::sources() {
            // Charge bytes and the already-reserved module slot before copying
            // and parsing the registry's actual ordinary source.
            total = total.checked_add(bundled.text().len()).ok_or_else(|| {
                Error::new("limit", Span::default(), "source byte count overflow")
            })?;
            if bundled.text().len() > MAX_SOURCE_BYTES || total > MAX_TOTAL_BYTES {
                return Err(Error::new(
                    "limit",
                    Span::default(),
                    "source exceeds 64 KiB per module or 1 MiB aggregate including std",
                ));
            }
            let module = Source::bundled(bundled, ParsePolicy::ExplicitModules)
                .map_err(Self::collection_error)?;
            collection.insert(module).map_err(|duplicate| {
                Error::new(
                    "module",
                    Span::default(),
                    format!("duplicate module {duplicate}"),
                )
            })?;
        }
        let sources = collection.finish();
        let originals = sources
            .iter()
            .map(|(name, source)| (name, source.syntax()))
            .collect();
        let (checked, (projections, meaning_targets)) = super::check::program_with_sources(
            originals,
            sources
                .iter()
                .map(|(name, source)| (name, source.text()))
                .collect(),
            super::check::SourceLimits::selected(),
            |resolution, interfaces, helpers, _, order, indices, budget, nominals| {
                let meaning_targets =
                    meaning::validate(&sources, resolution, interfaces, indices, order, budget)?;
                let mut projections = BTreeMap::new();
                for (id, declaration) in resolution.declarations() {
                    let original = &sources
                        .get(&declaration.name.0)
                        .expect("retained original")
                        .syntax()
                        .decls[declaration.ast_index];
                    budget.charge(original.span, 1)?;
                    if original.kind == super::ast::FnKind::Static {
                        continue;
                    }
                    let result = projection::project_declaration(
                        original,
                        &indices[&id],
                        helpers,
                        budget,
                        nominals,
                    )
                    .map_err(|e| e.in_module(&declaration.name.0));
                    if let Err(error) = &result {
                        if error.code == "limit" {
                            return Err(super::check::SourceError::from(error.clone()));
                        }
                    }
                    projections.insert(id, result);
                }
                Ok((projections, meaning_targets))
            },
        )
        .map_err(Error::from)?;
        let projections = projections
            .into_iter()
            .map(|(id, projected)| {
                let function = projected.map(|body| {
                    Arc::new(body.finish(Arc::clone(&checked.lexical[&id]), checked.effects[&id]))
                });
                (id, function)
            })
            .collect();
        Ok(Self {
            edition,
            manifests: Arc::new(manifests),
            sources: Arc::new(sources),
            checked: Arc::new(checked),
            projections: Arc::new(projections),
            meaning_targets: Arc::new(meaning_targets),
        })
    }

    /// Load explicitly mapped module files with the same limits as `parse`.
    /// No directory search or ambient module path influences import resolution.
    pub fn load(files: BTreeMap<String, PathBuf>) -> Result<Self> {
        Self::supplied_module_count(files.len())?;
        let mut sources = BTreeMap::new();
        let mut manifests = BTreeMap::new();
        let mut by_path: BTreeMap<PathBuf, Arc<super::project::EditionManifest>> = BTreeMap::new();
        let mut edition = None;
        let mut total = Self::bundled_bytes()?;
        for (name, path) in files {
            let selected = super::project::SourceFileSelection::select(&path).map_err(|e| {
                Error::new(
                    e.code,
                    e.primary.map_or(Span::default(), |p| p.span),
                    e.message,
                )
                .in_module(&name)
            })?;
            let manifest = selected.manifest();
            let captured = if let Some(previous) = by_path.get(manifest.path()) {
                if previous.as_ref() != manifest {
                    return Err(Error::new(
                        "edition",
                        Span::default(),
                        "manifest changed during source loading",
                    )
                    .in_module(&name));
                }
                Arc::clone(previous)
            } else {
                total = total.checked_add(manifest.source().len()).ok_or_else(|| {
                    Error::new("limit", Span::default(), "manifest byte count overflow")
                })?;
                let captured = Arc::new(manifest.clone());
                by_path.insert(manifest.path().into(), Arc::clone(&captured));
                captured
            };
            if edition.is_some_and(|previous| previous != captured.edition()) {
                return Err(Error::new(
                    "edition",
                    Span::default(),
                    "mixed captured constitutional editions",
                )
                .in_module(&name));
            }
            edition = Some(captured.edition());
            let remaining = MAX_TOTAL_BYTES.checked_sub(total).ok_or_else(|| {
                Error::new("limit", Span::default(), "source byte count overflow")
            })?;
            let source = selected
                .read(super::project::SourcePolicy::Bounded {
                    source_bytes: MAX_SOURCE_BYTES as u64,
                    project_bytes: remaining as u64,
                })
                .map_err(|e| {
                    Error::new(
                        e.code,
                        e.primary.map_or(Span::default(), |p| p.span),
                        e.message,
                    )
                    .in_module(&name)
                })?;
            total = total.checked_add(source.len()).ok_or_else(|| {
                Error::new("limit", Span::default(), "source byte count overflow")
            })?;
            if source.len() > MAX_SOURCE_BYTES || total > MAX_TOTAL_BYTES {
                return Err(
                    Error::new("limit", Span::default(), "source exceeds byte limit")
                        .in_module(&name),
                );
            }
            manifests.insert(name.clone(), captured);
            sources.insert(name, (Some(path), source));
        }
        let edition = edition.ok_or_else(|| {
            Error::new(
                "edition",
                Span::default(),
                "no source manifest selects an edition",
            )
        })?;
        Self::parse_inputs(edition, sources, manifests)
    }

    fn collection_error(failure: source::Failure) -> Error {
        let span = failure.span();
        let (code, message) = match failure.kind {
            source::FailureKind::ReservedModule => ("module", "invalid module path".into()),
            source::FailureKind::Parse(error) => {
                let code = if error.message.contains("limit")
                    || error.message.starts_with("source exceeds")
                {
                    "limit"
                } else {
                    "parse"
                };
                (code, error.message)
            }
        };
        Error::new(code, span, message).in_module(&failure.name)
    }

    fn definition(&self, id: DefId) -> Result<(&str, &Arc<ast::Function>)> {
        let declaration = self.checked.resolution.declaration(id);
        match &self.projections[&id] {
            Ok(function) => Ok((&declaration.name.0, function)),
            Err(error) => Err(error.clone()),
        }
    }

    fn resolution_error(failure: Failure) -> Error {
        let (code, message) = match failure.kind {
            FailureKind::InvalidPath => ("module", "definition path needs module::function".into()),
            FailureKind::MissingModule(module) => {
                ("module", format!("missing dependency module {module}"))
            }
            FailureKind::MissingName { module, name }
            | FailureKind::UnknownPrimitive { module, name } => {
                ("name", format!("no function {module}::{name}"))
            }
            FailureKind::Private(path) => ("visibility", format!("dependency {path} is private")),
            FailureKind::Collision(_) => ("name", "import shadows the local function".into()),
            FailureKind::DuplicateImport(name) => {
                ("name", format!("ambiguous imported name {name}"))
            }
            FailureKind::Duplicate(name) => ("name", format!("duplicate declaration {name}")),
            FailureKind::ExportCycle(path) => {
                ("name", format!("public reexport cycle at `{path}`"))
            }
            FailureKind::PreludePrimitive(name) => (
                "name",
                format!("std::prelude cannot reexport language primitive spelling `{name}`"),
            ),
            FailureKind::NotFunction(name) => {
                ("type", format!("`{name}` is a type, not a function"))
            }
            FailureKind::EmptyEnum(name) => (
                "type",
                format!("finite enum `{name}` must have at least one variant"),
            ),
            FailureKind::DuplicateMember { owner, member } => (
                "type",
                format!("duplicate member `{member}` in type `{owner}`"),
            ),
        };
        Error::new(code, failure.span, message).in_module(&failure.module)
    }

    /// Complete original text, including comments and line endings.
    pub fn source(&self, module: &str) -> Option<&str> {
        self.sources.get(module).map(Source::text)
    }

    /// Inspect the implementation principal, assertion and checked public effect.
    /// `inferred()` is diagnostic/internal source information: external callers
    /// and host-selected public providers must use `public_effect()` exclusively
    /// for their source contract and eligibility. A sharper inspected body effect
    /// cannot grant a capability hidden by that public bound. Private definitions
    /// remain inspectable metadata, not externally selectable entries.
    /// These facts supply neither native acceptance nor mathematical Meaning.
    pub fn function_effect(&self, path: &str) -> Option<super::effects::FunctionEffect> {
        let id = self.checked.resolution.qualified(path).ok()?;
        self.checked.effects.get(&id).copied()
    }

    /// The checked exported effect for one public source declaration.
    /// Private, absent or unchecked declarations have no exported contract.
    /// This does not grant inverse/control, Meaning, cleanup or execution evidence.
    pub fn public_function_effect(&self, path: &str) -> Option<crate::ir::Effect> {
        self.function_effect(path)?.public_effect()
    }

    pub fn module_names(&self) -> impl Iterator<Item = &str> {
        self.sources.iter().map(|(name, _)| name)
    }

    /// Check concrete entry bindings. This records an untrusted specialization
    /// request, not an elaborated body, executable circuit, or semantic proof.
    /// The host-selected entry must be public. Providers obey ordinary module
    /// visibility from that entry's module, even when unused by its body.
    pub fn instantiate(
        &self,
        entry: &str,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, OperationBinding>,
    ) -> Result<Instantiation> {
        self.instantiate_with_types(entry, BTreeMap::new(), naturals, operations)
    }

    /// Resolve an untrusted host Basis description against these original public
    /// types/reexports. Bindings are rechecked by the receiving preparation;
    /// this grants no runtime value, native acceptance or source preservation.
    pub fn basis_binding(&self, source: &str) -> Result<BasisBinding> {
        basis_binding::parse(source, Some(self))
    }

    /// Explicit closed Basis, Nat and provider bindings. Generic declarations
    /// have already been checked independently of these concrete choices.
    pub fn instantiate_with_types(
        &self,
        entry: &str,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, OperationBinding>,
    ) -> Result<Instantiation> {
        self.instantiate_prepared(entry, types, naturals, operations, true)
    }

    /// Whether the original collection contains nominal finite declarations.
    /// Source-feature selection grants no concrete eligibility or acceptance.
    pub fn requires_typed_ordinary_transport(&self) -> bool {
        !self.checked.nominals.is_empty()
    }

    /// Check all host bindings without requiring the legacy body projection.
    /// The original common judgment is retained. Actual ordinary execution
    /// still requires `compile_ordinary_with_kernel`; legacy `elaborate` retains
    /// its own body and transport refusals. No generic native route is enabled.
    pub fn instantiate_ordinary_with_types(
        &self,
        entry: &str,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, OperationBinding>,
    ) -> Result<Instantiation> {
        self.instantiate_prepared(entry, types, naturals, operations, false)
    }

    /// Prepare a full runtime interface without the legacy body projection.
    /// This checks host bindings only; `compile_runtime_with_kernel` must obtain
    /// a fresh native decision before execution. Generic native roots still refuse.
    pub fn instantiate_runtime_with_types(
        &self,
        entry: &str,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, OperationBinding>,
    ) -> Result<Instantiation> {
        self.instantiate_prepared(entry, types, naturals, operations, false)
    }

    fn instantiate_prepared(
        &self,
        entry: &str,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, OperationBinding>,
        require_entry_projection: bool,
    ) -> Result<Instantiation> {
        let (entry_id, operation_ids) = bindings::instantiate(
            self,
            entry,
            &types,
            &naturals,
            &operations,
            require_entry_projection,
        )?;
        Ok(Instantiation {
            program: self.clone(),
            entry: entry.into(),
            entry_id,
            operation_ids,
            types,
            naturals,
            operations,
        })
    }
}

/// An exact, closed ordinary basis tree, not a runtime value or an accepted IR
/// handle. Parsing preserves Unit/Bit/Bits tags, tuple arity, order and nesting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasisBinding {
    ty: SourceType,
    // Original host description, re-resolved in every receiving preparation.
    selection: Option<Arc<basis_binding::Selection>>,
}
impl BasisBinding {
    fn checked(ty: SourceType, span: Span) -> Result<Self> {
        if ty.storage_size(4096, 64).is_none() || ty.basis_width().is_none_or(|n| n > 8) {
            return Err(Error::new(
                "limit",
                span,
                "closed Basis binding exceeds eight bits or type storage capacity",
            ));
        }
        Ok(Self {
            ty,
            selection: None,
        })
    }
    /// The bounded selected-source profile permits at most eight total basis
    /// bits and retains its 4096-node/depth-64 type-storage limits.
    pub fn parse(source: &str) -> Result<Self> {
        basis_binding::parse(source, None)
    }
    pub fn ty(&self) -> &SourceType {
        &self.ty
    }
    fn key(&self) -> String {
        self.ty.display(super::types::Stage::Basis).to_string()
    }
    // Existing structural key accounting predates source-bound names. Charge
    // their variable-size canonical paths before allocating any cache key.
    fn named_key_cells(&self) -> usize {
        fn cells(ty: &SourceType) -> usize {
            match &ty.kind {
                super::types::Kind::Nominal(n) => n
                    .origin
                    .module
                    .len()
                    .saturating_add(n.origin.name.len())
                    .saturating_add(2),
                super::types::Kind::Tuple(fields) => fields
                    .iter()
                    .fold(0usize, |total, ty| total.saturating_add(cells(ty))),
                _ => 0,
            }
        }
        cells(&self.ty)
    }
}

/// A transparent operation provider with concrete natural arguments. Providers
/// requiring operation arguments are outside this entry-binding profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationBinding {
    definition: String,
    naturals: BTreeMap<String, u32>,
    types: BTreeMap<String, BasisBinding>,
}
impl OperationBinding {
    pub fn new(definition: impl Into<String>, naturals: BTreeMap<String, u32>) -> Self {
        Self::with_types(definition, BTreeMap::new(), naturals)
    }
    /// Provider type arguments belong to the provider's declaration, separately
    /// from its naturals and the entry's type arguments.
    pub fn with_types(
        definition: impl Into<String>,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
    ) -> Self {
        Self {
            definition: definition.into(),
            naturals,
            types,
        }
    }
    pub fn definition(&self) -> &str {
        &self.definition
    }
    pub fn naturals(&self) -> &BTreeMap<String, u32> {
        &self.naturals
    }
    pub fn types(&self) -> &BTreeMap<String, BasisBinding> {
        &self.types
    }
}

/// Retained source plus validated entry bindings; no lowering or acceptance seal.
#[derive(Clone, Debug)]
pub struct Instantiation {
    program: ParsedProgram,
    entry: String,
    entry_id: DefId,
    operation_ids: BTreeMap<String, DefId>,
    naturals: BTreeMap<String, u32>,
    types: BTreeMap<String, BasisBinding>,
    operations: BTreeMap<String, OperationBinding>,
}
impl Instantiation {
    /// Compile a nongeneric exported ordinary root through the common emitter
    /// and the fresh native ordinary-v2 request/decoded-view check. Every source
    /// declaration remains checked; native scope is the selected root only.
    pub fn compile_ordinary_with_kernel(
        &self,
        kernel: &crate::interchange::native::Kernel,
    ) -> std::result::Result<super::compile::SelectedOrdinaryProgram, super::diagnostic::Diagnostic>
    {
        super::compile::selected::compile(self, &self.program.sources, kernel, true)
    }

    /// Compile a nongeneric selected runtime interface, retaining ordinary
    /// fields and complete quantum owners through the same original-source
    /// emitter. Native checking binds its full types, storage and actual Raw
    /// body; source/runtime preservation remains a separate obligation.
    pub fn compile_runtime_with_kernel(
        &self,
        kernel: &crate::interchange::native::Kernel,
    ) -> std::result::Result<super::compile::SelectedRuntimeProgram, super::diagnostic::Diagnostic>
    {
        super::compile::selected::compile(self, &self.program.sources, kernel, false)
    }

    /// Elaborate bounded concrete source bodies into an untrusted, source-order
    /// ownership proposal. No IR verification seal or execution authority is made.
    pub fn elaborate(&self) -> Result<ElaboratedProgram> {
        elaborate::elaborate(self)
    }
    pub fn program(&self) -> &ParsedProgram {
        &self.program
    }
    pub fn entry(&self) -> &str {
        &self.entry
    }
    pub fn naturals(&self) -> &BTreeMap<String, u32> {
        &self.naturals
    }
    pub fn operations(&self) -> &BTreeMap<String, OperationBinding> {
        &self.operations
    }
    pub fn types(&self) -> &BTreeMap<String, BasisBinding> {
        &self.types
    }
}

fn valid_module_name(name: &str) -> bool {
    !name.is_empty()
        && name.split("::").all(|part| {
            let mut bytes = part.bytes();
            bytes
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
                && bytes.all(|c| c.is_ascii_alphanumeric() || c == b'_')
        })
        && !name.starts_with("std::")
        && name != "std"
}
