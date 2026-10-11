//! Internal preparation for bounded source specialization and lowering.
//!
//! Parsing, resolution, types, ownership and effects belong to the common
//! frontend. This adapter consumes that judgment, closes supplied bindings and
//! projects bodies into its concrete lowering representation. Preparation values
//! are not verified IR, execution handles or evidence of source preservation.

mod ast;
mod bindings;
mod elaborate;
mod lower;
mod meaning;
mod primitive;
mod projection;
mod qpe;
mod raw;

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
pub use raw::{CheckedSourceMeanings, RawSourceProposal, SourceMeaningCheck};

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
    pub fn parse(sources: BTreeMap<String, String>) -> Result<Self> {
        // Reject before constructing the path-bearing adapter map. The caller
        // may supply an oversized map; its count must not trigger another one.
        Self::supplied_module_count(sources.len())?;
        Self::parse_inputs(
            sources
                .into_iter()
                .map(|(name, text)| (name, (None, text)))
                .collect(),
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

    fn parse_inputs(sources: BTreeMap<String, (Option<PathBuf>, String)>) -> Result<Self> {
        Self::supplied_module_count(sources.len())?;
        super::project::check_bundled_manifest().map_err(|e| {
            Error::new(
                e.code,
                e.primary.map_or(Span::default(), |p| p.span),
                e.message,
            )
        })?;
        let mut total = 0usize;
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
        let (checked, (projections, meaning_targets)) = super::check::program_with(
            originals,
            super::check::SourceLimits::selected(),
            |resolution, interfaces, helpers, _, order, indices, budget| {
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
                    let result =
                        projection::project_declaration(original, &indices[&id], helpers, budget)
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
        let mut total = Self::bundled_bytes()?;
        for (name, path) in files {
            let remaining = MAX_TOTAL_BYTES.checked_sub(total).ok_or_else(|| {
                Error::new("limit", Span::default(), "source byte count overflow")
            })?;
            let source = super::project::read_source_file(
                &path,
                super::project::SourcePolicy::Bounded {
                    source_bytes: MAX_SOURCE_BYTES as u64,
                    project_bytes: remaining as u64,
                },
            )
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
            sources.insert(name, (Some(path), source));
        }
        Self::parse_inputs(sources)
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
        };
        Error::new(code, failure.span, message).in_module(&failure.module)
    }

    /// Complete original text, including comments and line endings.
    pub fn source(&self, module: &str) -> Option<&str> {
        self.sources.get(module).map(Source::text)
    }

    /// Principal and asserted effects from complete generic source checking.
    /// Private definitions are inspectable metadata, not selectable entries.
    /// This does not supply native acceptance or mathematical Meaning evidence.
    pub fn function_effect(&self, path: &str) -> Option<super::effects::FunctionEffect> {
        let id = self.checked.resolution.qualified(path).ok()?;
        self.checked.effects.get(&id).copied()
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

    /// Explicit closed Basis, Nat and provider bindings. Generic declarations
    /// have already been checked independently of these concrete choices.
    pub fn instantiate_with_types(
        &self,
        entry: &str,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, OperationBinding>,
    ) -> Result<Instantiation> {
        let (entry_id, operation_ids) =
            bindings::instantiate(self, entry, &types, &naturals, &operations)?;
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
        Ok(Self { ty })
    }
    /// The bounded selected-source profile permits at most eight total basis
    /// bits and retains its 4096-node/depth-64 type-storage limits.
    pub fn parse(source: &str) -> Result<Self> {
        let syntax = super::parser::parse_closed_basis(source)
            .map_err(|e| Error::new("type", e.span, e.message))?;
        struct Closed;
        impl super::types::SourceTypeContext for Closed {
            type Size = u32;
            type Error = Error;
            fn resolve_size(&mut self, n: &super::ast::Natural) -> Result<u32> {
                use super::ast::NatKind;
                let bad = || {
                    Error::new(
                        "type",
                        n.span,
                        "closed Basis size must be a bounded nonnegative u32 expression",
                    )
                };
                match &n.kind {
                    NatKind::Number(n) => u32::try_from(*n).map_err(|_| bad()),
                    NatKind::Name(_) | NatKind::Call { .. } => Err(bad()),
                    NatKind::Add(a, b) => self
                        .resolve_size(a)?
                        .checked_add(self.resolve_size(b)?)
                        .ok_or_else(bad),
                    NatKind::Sub(a, b) => self
                        .resolve_size(a)?
                        .checked_sub(self.resolve_size(b)?)
                        .ok_or_else(bad),
                    NatKind::Mul(a, b) => self
                        .resolve_size(a)?
                        .checked_mul(self.resolve_size(b)?)
                        .ok_or_else(bad),
                }
            }
            fn resolve_basis(&mut self, name: &super::ast::Ident) -> Result<SourceType> {
                Err(Error::new(
                    "type",
                    name.span,
                    format!(
                        "closed Basis binding cannot contain named type {}",
                        name.text
                    ),
                ))
            }
            fn quantum_basis_error(&mut self, span: Span) -> Error {
                Error::new(
                    "type",
                    span,
                    "closed Basis binding must be an ordinary type, not a Q owner",
                )
            }
            fn checked_node(
                &mut self,
                source: &super::ast::Type,
                _stage: super::types::Stage,
                ty: &SourceType,
            ) -> Result<()> {
                if ty.storage_size(4096, 64).is_none() || ty.basis_width().is_none_or(|n| n > 8) {
                    return Err(Error::new(
                        "limit",
                        source.span,
                        "closed Basis binding exceeds eight bits or type storage capacity",
                    ));
                }
                Ok(())
            }
        }
        let ty = super::types::classify_source(&syntax, super::types::Stage::Basis, &mut Closed)?;
        Self::checked(ty, syntax.span)
    }
    pub fn ty(&self) -> &SourceType {
        &self.ty
    }
    fn key(&self) -> String {
        self.ty.display(super::types::Stage::Basis).to_string()
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
