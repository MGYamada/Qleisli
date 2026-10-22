//! Root-relative module discovery and import resolution for `.qli` sources.
//!
//! This phase checks paths, declarations, import visibility and cycles. It is
//! not a type checker: a resolved source name cannot bypass IR verification.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::edition::Edition;

use super::ast::{self, FnKind, Span};
use super::diagnostic::{Diagnostic, SourceLocation, coordinates};
use super::lexer::keyword_kind;
use super::source::{self, BundledRegistry, ParsePolicy, Source};

mod edition;
mod manifest;
mod source_file;

pub use edition::EditionManifest;
pub use manifest::{QrateSource, manifest_warnings, qrate_source_root};

pub(super) fn check_bundled_manifest() -> Result<(), Diagnostic> {
    edition::check_bundled().map_err(LoadFailure::into_diagnostic)
}

/// Read-only metadata for this linked library's embedded standard qrate.
///
/// Construction validates the existing embedded manifest's schema, edition,
/// name and complete product version. This is not source checking, an accepted
/// program, authenticated distribution identity or native binary attestation.
#[derive(Clone, Copy, Debug)]
pub struct BundledStd {
    _validated: (),
}

/// Describe the actual embedded standard qrate after its existing manifest gate.
///
/// This uses no filesystem or runtime selection. Ordinary source and native
/// checks remain separate and fresh; only the immutable manifest gate is cached.
pub fn bundled_std() -> Result<BundledStd, Diagnostic> {
    check_bundled_manifest()?;
    Ok(BundledStd { _validated: () })
}

impl BundledStd {
    /// Complete product version of the linked Qleisli library.
    pub fn product_version(&self) -> &'static str {
        env!("CARGO_PKG_VERSION")
    }

    /// Canonical qrate name, verified by the embedded manifest gate.
    pub fn name(&self) -> &'static str {
        "std"
    }

    /// Complete std version, verified equal to the linked product version.
    pub fn version(&self) -> &'static str {
        env!("CARGO_PKG_VERSION")
    }

    /// Constitutional edition verified by the embedded manifest gate.
    pub fn edition(&self) -> &'static str {
        Edition::E2026.as_str()
    }

    /// Exact embedded manifest text, without reserialization or normalization.
    pub fn manifest(&self) -> &'static str {
        BundledRegistry::manifest()
    }

    /// Every embedded module's canonical name and exact, unmodified source.
    ///
    /// These are the same registry entries consumed by ordinary source loading.
    /// Their text has not been type-checked merely by obtaining this descriptor.
    pub fn modules(&self) -> impl ExactSizeIterator<Item = (&'static str, &'static str)> {
        BundledRegistry::sources()
            .iter()
            .map(|source| (source.name(), source.text()))
    }
}

/// Byte policy before UTF-8 decoding. Bounded project loading also permits at
/// most max(64, project_bytes / 1024) directory entries, including empty files.
/// Retained manifest text shares the aggregate project byte budget; each
/// actually read manifest is charged once, independently of the source-file cap.
/// Entry accounting is separate from input bytes. The legacy adapter is
/// explicit; parser, evidence and lowering budgets are independent of this.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourcePolicy {
    Legacy,
    Bounded {
        source_bytes: u64,
        project_bytes: u64,
    },
}

impl Default for SourcePolicy {
    fn default() -> Self {
        Self::Bounded {
            source_bytes: 1 << 20,
            project_bytes: 16 << 20,
        }
    }
}

struct SourceBudget {
    policy: SourcePolicy,
    used: u64,
}

impl SourceBudget {
    fn charge_manifest(&mut self, path: &Path, bytes: u64) -> Result<(), LoadFailure> {
        if let SourcePolicy::Bounded { project_bytes, .. } = self.policy {
            let total = self.used.checked_add(bytes)
                .filter(|total| *total <= project_bytes)
                .ok_or_else(|| Self::limit(path, format!("project exceeds {project_bytes}-byte aggregate source and manifest limit")))?;
            self.used = total;
        }
        Ok(())
    }

    fn limit(path: &Path, message: impl Into<String>) -> LoadFailure {
        let mut failure = error(path, Span::default(), message);
        failure.code = "limit";
        failure
    }

    fn allowance(&self, path: &Path) -> Result<Option<u64>, LoadFailure> {
        match self.policy {
            SourcePolicy::Legacy => Ok(None),
            SourcePolicy::Bounded {
                source_bytes,
                project_bytes,
            } => {
                if source_bytes == 0 || project_bytes == 0 {
                    return Err(Self::limit(path, "source byte limits must be positive"));
                }
                let remaining = project_bytes
                    .checked_sub(self.used)
                    .ok_or_else(|| Self::limit(path, "aggregate source byte limit exceeded"))?;
                Ok(Some(source_bytes.min(remaining)))
            }
        }
    }

    fn charge(&mut self, path: &Path, bytes: u64) -> Result<(), LoadFailure> {
        if let SourcePolicy::Bounded {
            source_bytes,
            project_bytes,
        } = self.policy
        {
            self.allowance(path)?;
            if bytes > source_bytes {
                return Err(Self::limit(
                    path,
                    format!("source exceeds {source_bytes}-byte file limit"),
                ));
            }
            let total = self
                .used
                .checked_add(bytes)
                .ok_or_else(|| Self::limit(path, "source byte accounting overflow"))?;
            if total > project_bytes {
                return Err(Self::limit(
                    path,
                    format!("project exceeds {project_bytes}-byte aggregate limit"),
                ));
            }
            self.used = total;
        }
        Ok(())
    }

    fn read(&mut self, path: &Path) -> Result<String, LoadFailure> {
        let file = source_file::open(path).map_err(|failure| io_error(path, failure))?;
        self.read_open(path, file)
    }

    fn read_open(&mut self, path: &Path, file: fs::File) -> Result<String, LoadFailure> {
        let allowance = self.allowance(path)?;
        if !file.metadata().map_err(|e| io_error(path, e))?.is_file() {
            return Err(error(
                path,
                Span::default(),
                "source must be a regular file",
            ));
        }
        let mut bytes = Vec::new();
        match allowance {
            Some(limit) => {
                let sentinel = limit
                    .checked_add(1)
                    .ok_or_else(|| Self::limit(path, "source read limit overflow"))?;
                file.take(sentinel)
                    .read_to_end(&mut bytes)
                    .map_err(|failure| io_error(path, failure))?;
            }
            None => {
                let mut file = file;
                file.read_to_end(&mut bytes)
                    .map_err(|failure| io_error(path, failure))?;
            }
        }
        self.charge(path, bytes.len() as u64)?;
        String::from_utf8(bytes)
            .map_err(|_| error(path, Span::default(), "source file is not valid UTF-8"))
    }
}

/// Read a single documentation source with explicit byte limits. Unlike project
/// loading this does not include bundled modules, because none are loaded. The
/// retained selecting manifest still shares the aggregate input budget.
pub fn read_source_file(path: &Path, policy: SourcePolicy) -> Result<String, Diagnostic> {
    SourceFileSelection::select(path)?.read(policy)
}

/// One selected source path and its actual validated manifest. Selection is
/// configuration/provenance only; it is not an atomic content snapshot.
pub(crate) struct SourceFileSelection {
    path: PathBuf,
    manifest: EditionManifest,
}

impl SourceFileSelection {
    pub(crate) fn select(path: &Path) -> Result<Self, Diagnostic> {
        // The single-file command accepts ordinary parent aliases such as /tmp on
        // macOS. Resolve them before opening; never resolve the final source link.
        let parent = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let resolved = fs::canonicalize(parent)
            .map_err(|failure| io_error(path, failure).into_diagnostic())?
            .join(path.file_name().ok_or_else(|| {
                error(path, Span::default(), "source path has no file name").into_diagnostic()
            })?);
        let manifest =
            edition::read_directory(resolved.parent().expect("resolved file has a parent"))
                .map_err(LoadFailure::into_diagnostic)?;
        Ok(Self {
            path: resolved,
            manifest,
        })
    }

    pub(crate) fn manifest(&self) -> &EditionManifest {
        &self.manifest
    }

    pub(crate) fn read(&self, policy: SourcePolicy) -> Result<String, Diagnostic> {
        let mut budget = SourceBudget { policy, used: 0 };
        // Keep the initial sentinel-overflow refusal before retained manifest
        // bytes reduce the remaining allowance.
        if budget
            .allowance(&self.path)
            .map_err(LoadFailure::into_diagnostic)?
            == Some(u64::MAX)
        {
            return Err(
                SourceBudget::limit(&self.path, "source read limit overflow").into_diagnostic(),
            );
        }
        budget
            .charge_manifest(self.manifest.path(), self.manifest.source().len() as u64)
            .map_err(LoadFailure::into_diagnostic)?;
        budget
            .read(&self.path)
            .map_err(LoadFailure::into_diagnostic)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ModuleOrigin {
    Local,
    Bundled,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImportOrigin {
    Local,
    Bundled,
}

/// An explicitly imported ordinary source declaration. Language primitives
/// resolve without imports and never receive a library-origin label.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImportKind {
    Function(FnKind),
    Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedImport {
    pub module: String,
    pub name: String,
    pub kind: ImportKind,
    /// Original declaration span in `module`, separately from this import use.
    pub declaration_span: ast::Span,
    pub origin: ImportOrigin,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct SourceModule {
    pub name: String,
    pub path: PathBuf,
    pub source: String,
    pub ast: ast::Module,
    pub imports: BTreeMap<String, ResolvedImport>,
    pub origin: ModuleOrigin,
}

#[derive(Clone, Debug)]
pub struct Project {
    pub root: PathBuf,
    /// Local modules use root-relative names; bundled `std` source modules
    /// follow the same checks. Sealed quantum/observe primitives have no AST.
    pub modules: BTreeMap<String, SourceModule>,
    pub(crate) edition_context: ProjectEdition,
}

#[derive(Clone, Debug)]
pub(crate) enum ProjectEdition {
    Explicit(Edition),
    Files {
        root: PathBuf,
        selected: Arc<EditionManifest>,
        sources: BTreeMap<PathBuf, Arc<EditionManifest>>,
        modules: BTreeMap<String, (PathBuf, ModuleOrigin)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectError {
    pub path: PathBuf,
    /// Half-open UTF-8 byte range in `path`, or 0..0 for a path/I/O error.
    pub span: Span,
    pub message: String,
}

impl fmt::Display for ProjectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}..{}: {}",
            self.path.display(),
            self.span.start,
            self.span.end,
            self.message
        )
    }
}

impl std::error::Error for ProjectError {}

#[derive(Clone)]
pub(crate) struct LoadFailure {
    pub error: ProjectError,
    pub coordinates: Option<(usize, usize)>,
    code: &'static str,
}

impl LoadFailure {
    pub(crate) fn into_diagnostic(self) -> Diagnostic {
        // Path/I/O failures have no decoded source. Keep their file identity
        // with the documented empty span, at the start of the file.
        let (line, column) = self.coordinates.unwrap_or((1, 1));
        Diagnostic {
            code: self.code,
            // The legacy ProjectError has no category field and retains its
            // parse context. Structured diagnostics carry that category once.
            message: if self.code == "parse" {
                self.error
                    .message
                    .strip_prefix("parse error: ")
                    .unwrap_or(&self.error.message)
                    .to_owned()
            } else {
                self.error.message
            },
            primary: Some(SourceLocation {
                path: self.error.path,
                span: self.error.span,
                line,
                column,
            }),
        }
    }
}

fn source_error(module: &SourceModule, span: Span, message: impl Into<String>) -> LoadFailure {
    located_error(&module.path, &module.source, span, "project", message)
}

fn located_error(
    path: &Path,
    source: &str,
    span: Span,
    code: &'static str,
    message: impl Into<String>,
) -> LoadFailure {
    let mut failure = error(path, span, message);
    let (line, column) = coordinates(source, span);
    failure.code = code;
    failure.coordinates = Some((line, column));
    failure
}

fn error(path: &Path, span: Span, message: impl Into<String>) -> LoadFailure {
    let message = message.into();
    LoadFailure {
        error: ProjectError {
            path: path.to_path_buf(),
            span,
            message,
        },
        coordinates: None,
        code: "project",
    }
}

fn io_error(path: &Path, failure: std::io::Error) -> LoadFailure {
    error(path, Span::default(), failure.to_string())
}

impl Project {
    /// Construct untrusted in-memory modules with an explicit constitutional
    /// selection. Compilation reconstructs their source judgments afresh.
    /// This grants no manifest provenance, native acceptance or execution handle.
    pub fn from_modules(
        root: PathBuf,
        modules: BTreeMap<String, SourceModule>,
        edition: Edition,
    ) -> Self {
        Self {
            root,
            modules,
            edition_context: ProjectEdition::Explicit(edition),
        }
    }

    pub fn edition(&self) -> Edition {
        match &self.edition_context {
            ProjectEdition::Explicit(edition) => *edition,
            ProjectEdition::Files { selected, .. } => selected.edition(),
        }
    }

    /// Exact requested manifest associated with an originally loaded local
    /// source. In-memory and embedded modules have no user-file manifest claim.
    pub fn module_manifest(&self, name: &str) -> Option<&EditionManifest> {
        let module = self.modules.get(name)?;
        if module.origin != ModuleOrigin::Local {
            return None;
        }
        match &self.edition_context {
            ProjectEdition::Explicit(_) => None,
            ProjectEdition::Files {
                root,
                sources,
                modules,
                ..
            } if root == &self.root
                && module.name == name
                && modules.get(name).is_some_and(|(path, origin)| {
                    path == &module.path && origin == &module.origin
                }) =>
            {
                sources.get(&module.path).map(AsRef::as_ref)
            }
            ProjectEdition::Files { .. } => None,
        }
    }

    pub(super) fn validate_edition_context(&self) -> Result<(), LoadFailure> {
        if let ProjectEdition::Files {
            root,
            selected,
            sources,
            modules,
        } = &self.edition_context
        {
            if self.root != *root {
                return Err(error(
                    &self.root,
                    Span::default(),
                    "source root differs from its captured edition context",
                ));
            }
            if self.modules.len() != modules.len()
                || self.modules.iter().any(|(name, module)| {
                    module.name != *name
                        || !modules.get(name).is_some_and(|(path, origin)| {
                            path == &module.path && origin == &module.origin
                        })
                })
            {
                return Err(error(
                    &self.root,
                    Span::default(),
                    "source inventory differs from its captured edition context",
                ));
            }
            for module in self
                .modules
                .values()
                .filter(|m| m.origin == ModuleOrigin::Local)
            {
                if sources
                    .get(&module.path)
                    .is_none_or(|manifest| manifest.edition() != selected.edition())
                {
                    return Err(error(
                        &module.path,
                        Span::default(),
                        "source has no matching captured edition context",
                    ));
                }
            }
        }
        Ok(())
    }

    fn public_name_hint(&self, name: &str, excluded: &str) -> String {
        if let Some(hint) = super::resolve::retired_public_name_hint(excluded, name) {
            return hint.to_owned();
        }
        let mut candidates: Vec<_> = self
            .modules
            .values()
            .filter(|module| module.name != excluded)
            .filter(|module| {
                module
                    .ast
                    .decls
                    .iter()
                    .any(|decl| decl.public && decl.name.text == name)
            })
            .map(|module| format!("{}::{name}", module.name))
            .collect();
        candidates.sort();
        if candidates.is_empty() {
            super::resolve::PrimitiveId::lookup_unbound(name).map_or_else(String::new, |id| {
                format!(
                    "; help: call language primitive `{}` without an import",
                    id.spelling()
                )
            })
        } else {
            format!(
                "; help: public alternatives: {}",
                candidates
                    .into_iter()
                    .take(4)
                    .map(|path| format!("`use {path};`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }
    /// Compatibility adapter retaining the pre-0.2 unbounded byte loader.
    pub fn load(root: &Path) -> Result<Self, ProjectError> {
        Self::load_detailed(root).map_err(|failure| failure.error)
    }

    pub(crate) fn load_detailed(root: &Path) -> Result<Self, LoadFailure> {
        Self::load_detailed_with_policy(root, SourcePolicy::Legacy)
    }

    pub fn load_with_policy(root: &Path, policy: SourcePolicy) -> Result<Self, Diagnostic> {
        Self::load_detailed_with_policy(root, policy).map_err(LoadFailure::into_diagnostic)
    }

    pub(crate) fn load_detailed_with_policy(
        root: &Path,
        policy: SourcePolicy,
    ) -> Result<Self, LoadFailure> {
        let budget = SourceBudget { policy, used: 0 };
        budget.allowance(root)?;
        let root = fs::canonicalize(root).map_err(|failure| io_error(root, failure))?;
        Self::load_resolved(&root, policy)
    }

    // A qrate selection already has a canonical base and a checked relative
    // suffix. Re-canonicalizing it would erase a replacement symlink (#192).
    fn load_resolved(root: &Path, policy: SourcePolicy) -> Result<Self, LoadFailure> {
        let directory =
            source_file::open_directory(root).map_err(|failure| io_error(root, failure))?;
        Self::load_anchored(root, &directory, policy)
    }

    fn load_anchored(
        root: &Path,
        directory: &fs::File,
        policy: SourcePolicy,
    ) -> Result<Self, LoadFailure> {
        Self::load_anchored_with_manifest(root, directory, policy, None)
    }

    fn load_anchored_with_manifest(
        root: &Path,
        directory: &fs::File,
        policy: SourcePolicy,
        selected: Option<Arc<EditionManifest>>,
    ) -> Result<Self, LoadFailure> {
        let mut budget = SourceBudget { policy, used: 0 };
        budget.allowance(root)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let held = directory.metadata().map_err(|e| io_error(root, e))?;
            let current = source_file::open_directory(root)
                .and_then(|file| file.metadata())
                .map_err(|e| io_error(root, e))?;
            if (held.dev(), held.ino()) != (current.dev(), current.ino()) {
                return Err(error(
                    root,
                    Span::default(),
                    "selected source root was replaced",
                ));
            }
        }
        let root = root.to_path_buf();
        edition::check_bundled()?;
        let mut files = Vec::new();
        let mut edition_context =
            collect_qli_files(&root, directory, &mut budget, &mut files, selected)?;
        files.sort_by(|a, b| a.0.cmp(&b.0));

        let mut collection = source::Builder::default();
        for (path, source) in files {
            let name = local_module_name(&root, &path)?;
            let parsed = Source::local(name, Some(path), source, ParsePolicy::Project)
                .map_err(collection_error)?;
            check_declarations(&parsed)?;
            collection.insert(parsed).map_err(|name| {
                error(&root, Span::default(), format!("duplicate module `{name}`"))
            })?;
        }

        for bundled in BundledRegistry::sources() {
            budget.charge(Path::new(bundled.path()), bundled.text().len() as u64)?;
            let parsed =
                Source::bundled(bundled, ParsePolicy::Project).map_err(collection_error)?;
            check_declarations(&parsed)?;
            collection.insert(parsed).map_err(|name| {
                error(&root, Span::default(), format!("duplicate module `{name}`"))
            })?;
        }

        // Consume the collection into the public mutable compatibility view;
        // compilation must inspect that view afresh, not a stale parallel cache.
        let modules: BTreeMap<_, _> = collection
            .finish()
            .into_entries()
            .map(|entry| {
                let (name, path, source, ast, bundled) = entry.into_parts();
                let module = SourceModule {
                    name: name.clone(),
                    path: path.expect("filesystem and bundled sources have paths"),
                    source,
                    ast,
                    imports: BTreeMap::new(),
                    origin: if bundled {
                        ModuleOrigin::Bundled
                    } else {
                        ModuleOrigin::Local
                    },
                };
                (name, module)
            })
            .collect();
        if let ProjectEdition::Files {
            modules: retained, ..
        } = &mut edition_context
        {
            *retained = modules
                .iter()
                .map(|(name, module)| (name.clone(), (module.path.clone(), module.origin)))
                .collect();
        }
        let mut project = Self {
            root,
            modules,
            edition_context,
        };
        project.resolve_imports()?;
        Ok(project)
    }

    pub fn module(&self, name: &str) -> Option<&SourceModule> {
        self.modules.get(name)
    }

    pub(super) fn resolution(&self) -> Result<super::resolve::Resolution, LoadFailure> {
        use super::resolve::Resolution;
        let mut result = Resolution::new(
            self.modules
                .iter()
                .map(|(name, source)| (name.as_str(), &source.ast)),
        )
        .map_err(|failure| self.resolution_error(failure))?;
        for (name, source) in &self.modules {
            let module = result.module(name).expect("registered module");
            let scope = result
                .imports(module, &source.ast)
                .map_err(|failure| self.resolution_error(failure))?;
            result.set_scope(module, scope);
        }
        Ok(result)
    }

    fn resolution_error(&self, failure: super::resolve::Failure) -> LoadFailure {
        use super::resolve::FailureKind;
        let message = match failure.kind {
            FailureKind::InvalidPath => "import needs a module and a name".into(),
            FailureKind::MissingModule(module) => format!("missing module `{module}`"),
            FailureKind::MissingName { module, name } => format!(
                "module `{module}` has no name `{name}`{}",
                self.public_name_hint(&name, &module)
            ),
            FailureKind::UnknownPrimitive { module, name } => format!(
                "retired compiler-owned module `{module}` has no public name `{name}`{}",
                self.public_name_hint(&name, &module)
            ),
            FailureKind::Private(path) => format!("`{path}` is not public"),
            FailureKind::Collision(name) | FailureKind::DuplicateImport(name) => {
                format!("name `{name}` collides with another declaration or import")
            }
            FailureKind::Duplicate(name) => format!("duplicate declaration `{name}`"),
            FailureKind::ExportCycle(path) => format!("public reexport cycle at `{path}`"),
            FailureKind::PreludePrimitive(name) => {
                format!("std::prelude cannot reexport language primitive spelling `{name}`")
            }
            FailureKind::NotFunction(name) => format!("`{name}` is a type, not a function"),
            FailureKind::EmptyEnum(name) => {
                format!("finite enum `{name}` must have at least one variant")
            }
            FailureKind::DuplicateMember { owner, member } => {
                format!("duplicate member `{member}` in type `{owner}`")
            }
        };
        source_error(&self.modules[&failure.module], failure.span, message)
    }

    fn resolve_imports(&mut self) -> Result<(), LoadFailure> {
        use super::resolve::Target;
        let resolution = self.resolution()?;
        let mut scopes = BTreeMap::new();
        for (name, source) in &self.modules {
            let module = resolution.module(name).expect("registered module");
            let scope = resolution.scope(module);
            let mut imports = BTreeMap::new();
            for usage in &source.ast.uses {
                let local = &usage.path.last().expect("parsed import").text;
                let (owner, name, kind, origin, declaration_span) = match scope.imports[local] {
                    Target::Declaration(id) => {
                        let declaration = resolution.declaration(id);
                        let (owner, name) = &declaration.name;
                        let origin = match self.modules[owner].origin {
                            ModuleOrigin::Local => ImportOrigin::Local,
                            ModuleOrigin::Bundled => ImportOrigin::Bundled,
                        };
                        let span = self.modules[owner].ast.decls[declaration.ast_index].span;
                        (
                            owner.clone(),
                            name.clone(),
                            ImportKind::Function(declaration.kind),
                            origin,
                            span,
                        )
                    }
                    Target::Type(id) => {
                        let declaration = resolution.type_declaration(id);
                        let (owner, name) = &declaration.name;
                        let origin = match self.modules[owner].origin {
                            ModuleOrigin::Local => ImportOrigin::Local,
                            ModuleOrigin::Bundled => ImportOrigin::Bundled,
                        };
                        let span = self.modules[owner].ast.type_decls[declaration.ast_index].span;
                        (owner.clone(), name.clone(), ImportKind::Type, origin, span)
                    }
                    Target::Primitive(_) => {
                        return Err(source_error(
                            source,
                            usage.span,
                            "language primitives cannot be imported; call their bare spellings",
                        ));
                    }
                };
                imports.insert(
                    local.clone(),
                    ResolvedImport {
                        module: owner,
                        name,
                        kind,
                        declaration_span,
                        origin,
                        span: usage.span,
                    },
                );
            }
            scopes.insert(name.clone(), imports);
        }
        for (name, imports) in scopes {
            self.modules.get_mut(&name).expect("known module").imports = imports;
        }
        Ok(())
    }
}

fn collect_qli_files(
    root: &Path,
    anchor: &fs::File,
    budget: &mut SourceBudget,
    files: &mut Vec<(PathBuf, String)>,
    selected: Option<Arc<EditionManifest>>,
) -> Result<ProjectEdition, LoadFailure> {
    struct Directory {
        path: PathBuf,
        anchor: fs::File,
        entries: std::vec::IntoIter<std::ffi::OsString>,
        manifest: Arc<EditionManifest>,
    }
    fn enter(
        path: PathBuf,
        anchor: fs::File,
        root: bool,
        budget: &mut SourceBudget,
        entries_used: &mut u64,
        inherited: Option<Arc<EditionManifest>>,
    ) -> Result<Directory, LoadFailure> {
        let manifest = match edition::read_anchored(&path, &anchor)? {
            Some(manifest) => {
                budget.charge_manifest(manifest.path(), manifest.source().len() as u64)?;
                Arc::new(manifest)
            }
            None => match &inherited {
                Some(manifest) => Arc::clone(manifest),
                None if root => {
                    let manifest = edition::read_directory(path.parent().unwrap_or(&path))?;
                    budget.charge_manifest(manifest.path(), manifest.source().len() as u64)?;
                    Arc::new(manifest)
                }
                None => {
                    return Err(error(
                        &path,
                        Span::default(),
                        "missing inherited edition context",
                    ));
                }
            },
        };
        if inherited
            .as_ref()
            .is_some_and(|parent| parent.edition() != manifest.edition())
        {
            return Err(error(
                manifest.path(),
                Span::default(),
                "nested manifest has a different constitutional edition",
            ));
        }
        let mut entries = Vec::new();
        for entry in source_file::entries(&anchor, &path).map_err(|e| io_error(&path, e))? {
            let entry = entry.map_err(|e| io_error(&path, e))?;
            if let SourcePolicy::Bounded { project_bytes, .. } = budget.policy {
                let maximum = (project_bytes / 1024).max(64);
                *entries_used += 1;
                if *entries_used > maximum {
                    return Err(SourceBudget::limit(
                        &path.join(&entry),
                        format!("project directory-entry limit exceeded ({maximum} entries)"),
                    ));
                }
            }
            entries.push(entry);
        }
        entries.sort();
        Ok(Directory {
            path,
            anchor,
            entries: entries.into_iter(),
            manifest,
        })
    }
    let mut entries_used = 0;
    if let Some(manifest) = &selected {
        budget.charge_manifest(manifest.path(), manifest.source().len() as u64)?;
    }
    let directory = enter(
        root.to_owned(),
        anchor.try_clone().map_err(|e| io_error(root, e))?,
        true,
        budget,
        &mut entries_used,
        selected.clone(),
    )?;
    let selected = selected.unwrap_or_else(|| Arc::clone(&directory.manifest));
    let mut sources = BTreeMap::new();
    // Hold only the active ancestor chain, not one handle per sibling directory.
    // Discovery is iterative so directory depth cannot exhaust the Rust stack.
    let mut stack = vec![directory];
    while let Some(directory) = stack.last_mut() {
        let Some(name) = directory.entries.next() else {
            stack.pop();
            continue;
        };
        let path = directory.path.join(&name);
        match source_file::kind(&directory.anchor, &directory.path, &name)
            .map_err(|e| io_error(&path, e))?
        {
            source_file::Kind::Link => {
                return Err(error(
                    &path,
                    Span::default(),
                    "symlinks are not allowed in a source root",
                ));
            }
            source_file::Kind::Directory => {
                let child = source_file::child(&directory.anchor, &directory.path, &name, true)
                    .map_err(|e| io_error(&path, e))?;
                let inherited = Arc::clone(&directory.manifest);
                stack.push(enter(
                    path,
                    child,
                    false,
                    budget,
                    &mut entries_used,
                    Some(inherited),
                )?);
            }
            source_file::Kind::File if path.extension().is_some_and(|ext| ext == "qli") => {
                let file = source_file::child(&directory.anchor, &directory.path, &name, false)
                    .map_err(|e| io_error(&path, e))?;
                let source = budget.read_open(&path, file)?;
                sources.insert(path.clone(), Arc::clone(&directory.manifest));
                files.push((path, source));
            }
            source_file::Kind::File if path.extension().is_some_and(|ext| ext == "qlt") => {
                sources.insert(path, Arc::clone(&directory.manifest));
            }
            _ => {}
        }
    }
    Ok(ProjectEdition::Files {
        root: root.into(),
        selected,
        sources,
        modules: BTreeMap::new(),
    })
}

fn local_module_name(root: &Path, path: &Path) -> Result<String, LoadFailure> {
    let relative = path.strip_prefix(root).expect("collected beneath root");
    let mut parts = Vec::new();
    let file = relative.file_name().expect("collected file has a name");
    for component in relative.parent().into_iter().flat_map(Path::components) {
        let text = component
            .as_os_str()
            .to_str()
            .ok_or_else(|| error(path, Span::default(), "module path is not valid UTF-8"))?;
        if !valid_ident(text) {
            return Err(error(
                path,
                Span::default(),
                format!("invalid module path component `{text}`"),
            ));
        }
        parts.push(text.to_owned());
    }
    let file = file
        .to_str()
        .ok_or_else(|| error(path, Span::default(), "module path is not valid UTF-8"))?;
    let stem = file.strip_suffix(".qli").expect("collected .qli file");
    if !valid_ident(stem) {
        return Err(error(
            path,
            Span::default(),
            format!("invalid module path component `{stem}`"),
        ));
    }
    parts.push(stem.to_owned());
    if parts.first().is_some_and(|part| part == "std") {
        return Err(error(
            path,
            Span::default(),
            "`std::` is reserved for bundled modules",
        ));
    }
    Ok(parts.join("::"))
}

fn valid_ident(name: &str) -> bool {
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == b'_' && name.len() > 1)
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && keyword_kind(name).is_none()
}

fn collection_error(failure: source::Failure) -> LoadFailure {
    let span = failure.span();
    let (code, message) = match failure.kind {
        source::FailureKind::ReservedModule => {
            ("project", "local modules cannot occupy `std`".into())
        }
        source::FailureKind::Parse(error) => ("parse", format!("parse error: {}", error.message)),
    };
    located_error(
        failure.path.as_deref().expect("project source has a path"),
        &failure.text,
        span,
        code,
        message,
    )
}

fn check_declarations(module: &Source) -> Result<(), LoadFailure> {
    let mut seen = BTreeSet::new();
    for declaration in &module.syntax().decls {
        if !seen.insert(declaration.name.text.as_str()) {
            return Err(located_error(
                module.path().expect("project source has a path"),
                module.text(),
                declaration.name.span,
                "project",
                format!("duplicate declaration `{}`", declaration.name.text),
            ));
        }
    }
    Ok(())
}
