//! Additive, untrusted preparation of a bounded sized-source profile.
//!
//! These values retain source and report generic checking results. They are not
//! verified IR, execution handles, or evidence of source preservation. The finite
//! frontend shares its source parser and syntax tree with this profile.

mod ast;
mod check;
mod elaborate;
mod linear;
mod lower;
mod parser;
mod primitive;
mod qpe;

use super::resolve::{DefId, Failure, FailureKind, Resolution};
use std::collections::BTreeMap;
use std::fmt;
use std::path::PathBuf;

pub use super::ast::Span;
pub use elaborate::{
    ElaboratedProgram, SourceDefinition, SourceOperation, SourceStep, SourceType, SourceValue,
};
pub use lower::{
    FramePort, HierarchyProposal, InitializationMove, PreparationValidation, SourceEvent,
};

pub(super) fn primitive_path(path: &str) -> Option<&'static str> {
    primitive::Primitive::lookup(path).map(|p| p.signature().path)
}

type Result<T> = std::result::Result<T, Error>;
pub use qpe::QpeBindingProposal;
const MAX_MODULES: usize = 64;
const MAX_SOURCE_BYTES: usize = 65_536;
const MAX_TOTAL_BYTES: usize = 1_048_576;

/// A preparation failure, with a half-open byte span in the retained module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    code: &'static str,
    module: Option<String>,
    span: Span,
    message: String,
}
impl Error {
    fn new(code: &'static str, span: Span, message: impl Into<String>) -> Self {
        Self {
            code,
            module: None,
            span,
            message: message.into(),
        }
    }
    fn in_module(mut self, module: &str) -> Self {
        if self.module.is_none() {
            self.module = Some(module.into());
        }
        self
    }
    pub fn code(&self) -> &str {
        self.code
    }
    pub fn module(&self) -> Option<&str> {
        self.module.as_deref()
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn message(&self) -> &str {
        &self.message
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}..{}: {}: {}",
            self.module.as_deref().unwrap_or("<source>"),
            self.span.start,
            self.span.end,
            self.code,
            self.message
        )
    }
}
impl std::error::Error for Error {}

/// An opaque source collection with privately represented syntax and generic
/// preparation checks. Cloning this value does not create checked IR evidence.
#[derive(Clone, Debug)]
pub struct ParsedProgram {
    sources: BTreeMap<String, String>,
    syntax: BTreeMap<String, super::ast::Module>,
    modules: BTreeMap<String, ast::Module>,
    resolution: Resolution,
}
impl ParsedProgram {
    /// The retained common source AST. It is untrusted syntax, not checked IR.
    pub fn syntax(&self, module: &str) -> Option<&super::ast::Module> {
        self.syntax.get(module)
    }

    /// Parse and check every supplied module, including unused imports and both
    /// arms of static branches. Imports must resolve within this complete map or
    /// to a primitive explicitly specified by this bounded profile.
    pub fn parse(sources: BTreeMap<String, String>) -> Result<Self> {
        if sources.is_empty() || sources.len() > MAX_MODULES {
            return Err(Error::new(
                "limit",
                Span::default(),
                "provide 1 through 64 modules",
            ));
        }
        let mut total = 0usize;
        let mut modules = BTreeMap::new();
        let mut syntax = BTreeMap::new();
        for (name, source) in &sources {
            if !valid_module_name(name) {
                return Err(
                    Error::new("module", Span::default(), "invalid module path").in_module(name)
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
                .in_module(name));
            }
            let module = super::parser::parse_bounded_module(source).map_err(|e| {
                let code = if e.message.contains("limit") || e.message.starts_with("source exceeds")
                {
                    "limit"
                } else {
                    "parse"
                };
                Error::new(code, e.span, e.message).in_module(name)
            })?;
            let projected = parser::project(&module).map_err(|e| e.in_module(name))?;
            syntax.insert(name.clone(), module);
            modules.insert(name.clone(), projected);
        }
        let resolution = Resolution::new(syntax.iter().map(|(name, ast)| (name.as_str(), ast)))
            .map_err(Self::resolution_error)?;
        // Preserve the per-module profile diagnostic boundary above. Reuse the
        // same projection after real declaration IDs exist; no source reparse
        // or competing preflight rules are involved.
        for (id, declaration) in resolution.declarations() {
            let module = &syntax[&declaration.name.0];
            let index = super::resolve::locals::Index::new(
                id,
                &module.decls[declaration.ast_index],
                |_| None,
            );
            modules
                .get_mut(&declaration.name.0)
                .expect("projected module")
                .functions[declaration.ast_index] =
                parser::project_declaration(&module.decls[declaration.ast_index], Some(&index))
                    .map_err(|error| error.in_module(&declaration.name.0))?;
        }
        let mut program = Self {
            sources,
            syntax,
            modules,
            resolution,
        };
        check::program(&mut program)?;
        Ok(program)
    }

    /// Load explicitly mapped module files with the same limits as `parse`.
    /// No directory search or ambient module path influences import resolution.
    pub fn load(files: BTreeMap<String, PathBuf>) -> Result<Self> {
        if files.is_empty() || files.len() > MAX_MODULES {
            return Err(Error::new(
                "limit",
                Span::default(),
                "provide 1 through 64 modules",
            ));
        }
        let mut sources = BTreeMap::new();
        let mut total = 0usize;
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
            sources.insert(name, source);
        }
        Self::parse(sources)
    }

    fn definition(&self, id: DefId) -> (&str, &ast::Function) {
        let declaration = self.resolution.declaration(id);
        let (module, parsed) = self
            .modules
            .get_key_value(&declaration.name.0)
            .expect("resolved module");
        let function = &parsed.functions[declaration.ast_index];
        debug_assert_eq!(function.name, declaration.name.1);
        (module, function)
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
        self.sources.get(module).map(String::as_str)
    }
    pub fn module_names(&self) -> impl Iterator<Item = &str> {
        self.sources.keys().map(String::as_str)
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
        let (entry_id, operation_ids) = check::instantiate(self, entry, &naturals, &operations)?;
        Ok(Instantiation {
            program: self.clone(),
            entry: entry.into(),
            entry_id,
            operation_ids,
            naturals,
            operations,
        })
    }
}

/// A transparent operation provider with concrete natural arguments. Providers
/// requiring operation arguments are outside this entry-binding profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationBinding {
    definition: String,
    naturals: BTreeMap<String, u32>,
}
impl OperationBinding {
    pub fn new(definition: impl Into<String>, naturals: BTreeMap<String, u32>) -> Self {
        Self {
            definition: definition.into(),
            naturals,
        }
    }
    pub fn definition(&self) -> &str {
        &self.definition
    }
    pub fn naturals(&self) -> &BTreeMap<String, u32> {
        &self.naturals
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
