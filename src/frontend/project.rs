//! Root-relative module discovery and import resolution for `.qli` sources.
//!
//! This phase checks paths, declarations, import visibility and cycles. It is
//! not a type checker: a resolved source name cannot bypass IR verification.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

use super::ast::{self, FnKind, Span, UseDecl};
use super::diagnostic::{Diagnostic, SourceLocation, coordinates};
use super::lexer::keyword_kind;
use super::parser::parse_module;

mod edition;
mod manifest;
mod source_file;

pub use manifest::{QrateSource, manifest_warnings, qrate_source_root};

const BUNDLED_SOURCES: &[(&str, &str)] = &[
    (
        "arithmetic",
        include_str!("../../stdlib/src/arithmetic.qli"),
    ),
    ("basis", include_str!("../../stdlib/src/basis.qli")),
    ("routines", include_str!("../../stdlib/src/routines.qli")),
    (
        "transforms",
        include_str!("../../stdlib/src/transforms.qli"),
    ),
];

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
            Path::new("<bundled>/std/Qargo.toml"),
            include_str!("../../stdlib/Qargo.toml"),
        )?;
        let mut files = Vec::new();
        collect_qli_files(&root, directory, &mut budget, &mut files)?;
        files.sort_by(|a, b| a.0.cmp(&b.0));

        let mut modules = BTreeMap::new();
        for (path, source) in files {
            let name = local_module_name(&root, &path)?;
            let module = parse_source(name.clone(), path, ModuleOrigin::Local, source)?;
            if modules.insert(name.clone(), module).is_some() {
                return Err(error(
                    &root,
                    Span::default(),
                    format!("duplicate module `{name}`"),
                ));
            }
        }

        for &(name, source) in BUNDLED_SOURCES {
            let path = PathBuf::from(format!("<bundled>/std/{name}.qli"));
            budget.charge(&path, source.len() as u64)?;
            let ast = parse_module(source).map_err(|failure| {
                located_error(
                    &path,
                    source,
                    failure.span,
                    "parse",
                    format!("parse error: {}", failure.message),
                )
            })?;
            let module = SourceModule {
                name: format!("std::{name}"),
                path,
                source: source.to_owned(),
                ast,
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Bundled,
            };
            check_declarations(&module)?;
            modules.insert(module.name.clone(), module);
        }

        let mut project = Self { root, modules };
        project.resolve_imports()?;
        project.reject_cycles()?;
        Ok(project)
    }

    pub fn module(&self, name: &str) -> Option<&SourceModule> {
        self.modules.get(name)
    }

    fn resolve_imports(&mut self) -> Result<(), LoadFailure> {
        // Resolve against immutable module declarations first, then publish the
        // completed scopes. Declaration order cannot change import meaning.
        let mut scopes = BTreeMap::new();
        for (module_name, module) in &self.modules {
            let mut used_names: BTreeSet<&str> = module
                .ast
                .decls
                .iter()
                .map(|decl| decl.name.text.as_str())
                .collect();
            let mut imports = BTreeMap::new();
            for use_decl in &module.ast.uses {
                let imported = self.resolve_one_import(module, use_decl)?;
                let local_name = imported.name.clone();
                if !used_names.insert(&use_decl.path.last().expect("parser requires name").text) {
                    return Err(source_error(
                        module,
                        use_decl.path.last().expect("parser requires name").span,
                        format!("name `{local_name}` collides with another declaration or import"),
                    ));
                }
                imports.insert(local_name, imported);
            }
            scopes.insert(module_name.clone(), imports);
        }
        for (module_name, imports) in scopes {
            self.modules
                .get_mut(&module_name)
                .expect("module exists")
                .imports = imports;
        }
        Ok(())
    }

    fn resolve_one_import(
        &self,
        caller: &SourceModule,
        use_decl: &UseDecl,
    ) -> Result<ResolvedImport, LoadFailure> {
        let segments = &use_decl.path;
        if segments.len() < 2 {
            return Err(source_error(
                caller,
                use_decl.span,
                "import needs a module and a name",
            ));
        }
        let name = &segments.last().expect("nonempty import path").text;
        let source_module = segments[..segments.len() - 1]
            .iter()
            .map(|segment| segment.text.as_str())
            .collect::<Vec<_>>()
            .join("::");

        if source_module == "std::quantum" || source_module == "std::observe" {
            if let Some(kind) = sealed_kind(&source_module, name) {
                return Ok(ResolvedImport {
                    module: source_module,
                    name: name.clone(),
                    kind,
                    origin: ImportOrigin::Sealed,
                    span: use_decl.span,
                });
            }
            return Err(source_error(
                caller,
                segments.last().expect("nonempty import path").span,
                format!(
                    "sealed module `{source_module}` has no public name `{name}`{}",
                    self.public_name_hint(name, &source_module)
                ),
            ));
        }
        let target = self.modules.get(&source_module).ok_or_else(|| {
            source_error(
                caller,
                use_decl.span,
                format!("missing module `{source_module}`"),
            )
        })?;
        let declaration = target
            .ast
            .decls
            .iter()
            .find(|declaration| declaration.name.text == *name)
            .ok_or_else(|| {
                source_error(
                    caller,
                    segments.last().expect("nonempty import path").span,
                    format!(
                        "module `{source_module}` has no name `{name}`{}",
                        self.public_name_hint(name, &source_module)
                    ),
                )
            })?;
        if !declaration.public {
            return Err(source_error(
                caller,
                segments.last().expect("nonempty import path").span,
                format!("`{source_module}::{name}` is not public"),
            ));
        }
        Ok(ResolvedImport {
            module: source_module,
            name: name.clone(),
            kind: declaration.kind,
            origin: match target.origin {
                ModuleOrigin::Local => ImportOrigin::Local,
                ModuleOrigin::Bundled => ImportOrigin::Bundled,
            },
            span: use_decl.span,
        })
    }

    fn reject_cycles(&self) -> Result<(), LoadFailure> {
        let mut marks = BTreeMap::<&str, u8>::new();
        // Each frame records the next import to visit. Keep the active path on
        // the heap so a long acyclic module chain cannot exhaust the Rust stack.
        let mut stack = Vec::<(&str, usize)>::new();
        for name in self.modules.keys() {
            if marks.get(name.as_str()).copied() == Some(2) {
                continue;
            }
            marks.insert(name, 1);
            stack.push((name, 0));
            while let Some((name, next_import)) = stack.last_mut() {
                let module = self.modules.get(*name).expect("known module");
                let Some(use_decl) = module.ast.uses.get(*next_import) else {
                    marks.insert(*name, 2);
                    stack.pop();
                    continue;
                };
                *next_import += 1;
                let local_name = &use_decl.path.last().expect("parser requires name").text;
                let imported = module.imports.get(local_name).expect("imports resolved");
                if imported.origin == ImportOrigin::Sealed {
                    continue;
                }
                let dependency = imported.module.as_str();
                match marks.get(dependency).copied() {
                    Some(1) => {
                        let start = stack
                            .iter()
                            .position(|(name, _)| *name == dependency)
                            .expect("active module is on the DFS path");
                        let mut cycle: Vec<_> =
                            stack[start..].iter().map(|(name, _)| *name).collect();
                        cycle.push(dependency);
                        return Err(source_error(
                            module,
                            use_decl.span,
                            format!("cyclic import: {}", cycle.join(" -> ")),
                        ));
                    }
                    Some(2) => continue,
                    _ => {}
                }
                marks.insert(dependency, 1);
                stack.push((dependency, 0));
            }
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

fn parse_source(
    name: String,
    path: PathBuf,
    origin: ModuleOrigin,
    source: String,
) -> Result<SourceModule, LoadFailure> {
    let ast = parse_module(&source).map_err(|failure| {
        located_error(
            &path,
            &source,
            failure.span,
            "parse",
            format!("parse error: {}", failure.message),
        )
    })?;
    let module = SourceModule {
        name,
        path,
        source,
        ast,
        imports: BTreeMap::new(),
        origin,
    };
    check_declarations(&module)?;
    Ok(module)
}

fn check_declarations(module: &SourceModule) -> Result<(), LoadFailure> {
    let mut seen = BTreeSet::new();
    for declaration in &module.ast.decls {
        if !seen.insert(declaration.name.text.as_str()) {
            return Err(source_error(
                module,
                declaration.name.span,
                format!("duplicate declaration `{}`", declaration.name.text),
            ));
        }
    }
    Ok(())
}

fn sealed_kind(module: &str, name: &str) -> Option<FnKind> {
    super::core::primitive(module, name).map(|item| item.kind)
}
