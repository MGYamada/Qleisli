//! Root-relative module discovery and import resolution for `.qli` sources.
//!
//! This phase checks paths, declarations, import visibility and cycles. It is
//! not a type checker: a resolved source name cannot bypass IR verification.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

use super::ast::{self, FnKind, Span};
use super::diagnostic::{Diagnostic, SourceLocation, coordinates};
use super::lexer::keyword_kind;
use super::source::{self, BundledRegistry, ParsePolicy, Source};

mod edition;
mod manifest;
mod source_file;

pub use manifest::{QrateSource, manifest_warnings, qrate_source_root};

pub(super) fn check_bundled_manifest() -> Result<(), Diagnostic> {
    edition::check_manifest(
        Path::new(BundledRegistry::manifest_path()),
        BundledRegistry::manifest(),
    )
    .map_err(LoadFailure::into_diagnostic)
}

/// Byte policy before UTF-8 decoding. Bounded project loading also permits at
/// most max(64, project_bytes / 1024) directory entries, including empty files.
/// Entry accounting is separate from source bytes. The legacy adapter is
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
/// loading this does not include bundled modules, because none are loaded.
pub fn read_source_file(path: &Path, policy: SourcePolicy) -> Result<String, Diagnostic> {
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
    edition::check_directory(resolved.parent().expect("resolved file has a parent"))
        .map_err(LoadFailure::into_diagnostic)?;
    SourceBudget { policy, used: 0 }
        .read(&resolved)
        .map_err(LoadFailure::into_diagnostic)
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
    Sealed,
}

/// A name admitted to a module's top-level scope. `Sealed` is assigned only
/// by this resolver for known compiler primitives, never by a local `.qli`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedImport {
    pub module: String,
    pub name: String,
    pub kind: FnKind,
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
            message: self.error.message,
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
    fn public_name_hint(&self, name: &str, excluded: &str) -> String {
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
        candidates.extend(
            super::core::PRIMITIVES
                .iter()
                .filter(|item| item.name == name && item.module != excluded)
                .map(|item| format!("{}::{name}", item.module)),
        );
        candidates.sort();
        if candidates.is_empty() {
            String::new()
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
        edition::check_manifest(
            Path::new(BundledRegistry::manifest_path()),
            BundledRegistry::manifest(),
        )?;
        let mut files = Vec::new();
        collect_qli_files(&root, directory, &mut budget, &mut files)?;
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
        let modules = collection
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
        let mut project = Self { root, modules };
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
                "sealed module `{module}` has no public name `{name}`{}",
                self.public_name_hint(&name, &module)
            ),
            FailureKind::Private(path) => format!("`{path}` is not public"),
            FailureKind::Collision(name) | FailureKind::DuplicateImport(name) => {
                format!("name `{name}` collides with another declaration or import")
            }
            FailureKind::Duplicate(name) => format!("duplicate declaration `{name}`"),
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
                let (owner, name, kind, origin) = match scope.imports[local] {
                    Target::Declaration(id) => {
                        let declaration = resolution.declaration(id);
                        let (owner, name) = &declaration.name;
                        let origin = match self.modules[owner].origin {
                            ModuleOrigin::Local => ImportOrigin::Local,
                            ModuleOrigin::Bundled => ImportOrigin::Bundled,
                        };
                        (owner.clone(), name.clone(), declaration.kind, origin)
                    }
                    Target::Primitive(id) => (
                        id.module.into(),
                        id.name.into(),
                        sealed_kind(id.module, id.name).expect("resolved primitive"),
                        ImportOrigin::Sealed,
                    ),
                };
                imports.insert(
                    local.clone(),
                    ResolvedImport {
                        module: owner,
                        name,
                        kind,
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
) -> Result<(), LoadFailure> {
    struct Directory {
        path: PathBuf,
        anchor: fs::File,
        entries: std::vec::IntoIter<std::ffi::OsString>,
    }
    fn enter(
        path: PathBuf,
        anchor: fs::File,
        root: bool,
        policy: SourcePolicy,
        entries_used: &mut u64,
    ) -> Result<Directory, LoadFailure> {
        edition::check_anchored(&path, &anchor, root)?;
        let mut entries = Vec::new();
        for entry in source_file::entries(&anchor, &path).map_err(|e| io_error(&path, e))? {
            let entry = entry.map_err(|e| io_error(&path, e))?;
            if let SourcePolicy::Bounded { project_bytes, .. } = policy {
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
        })
    }
    let mut entries_used = 0;
    let directory = enter(
        root.to_owned(),
        anchor.try_clone().map_err(|e| io_error(root, e))?,
        true,
        budget.policy,
        &mut entries_used,
    )?;
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
                stack.push(enter(path, child, false, budget.policy, &mut entries_used)?);
            }
            source_file::Kind::File if path.extension().is_some_and(|ext| ext == "qli") => {
                let file = source_file::child(&directory.anchor, &directory.path, &name, false)
                    .map_err(|e| io_error(&path, e))?;
                let source = budget.read_open(&path, file)?;
                files.push((path, source));
            }
            _ => {} // QLT inherits the edition checked once above.
        }
    }
    Ok(())
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

fn sealed_kind(module: &str, name: &str) -> Option<FnKind> {
    let path = format!("{module}::{name}");
    super::check::primitive::Primitive::lookup(&path).map(|item| match item.effect() {
        crate::ir::Effect::Unitary => FnKind::Unitary,
        crate::ir::Effect::Iso => FnKind::Iso,
        crate::ir::Effect::Observe => FnKind::Observe,
    })
}
