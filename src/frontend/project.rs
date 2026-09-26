//! Root-relative module discovery and import resolution for `.qli` sources.
//!
//! This phase checks paths, declarations, import visibility and cycles. It is
//! not a type checker: a resolved source name cannot bypass IR verification.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use super::ast::{self, FnKind, Span, UseDecl};
use super::lexer::keyword_kind;
use super::parser::parse_module;

const BUNDLED_BASIS: &str = include_str!("../../stdlib/src/basis.qli");

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
    /// Local modules use root-relative names; `std::basis` is the bundled
    /// source module. Sealed `std::quantum` and `std::observe` have no AST.
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

fn error(path: &Path, span: Span, message: impl Into<String>) -> ProjectError {
    ProjectError {
        path: path.to_path_buf(),
        span,
        message: message.into(),
    }
}

fn io_error(path: &Path, failure: std::io::Error) -> ProjectError {
    error(path, Span::default(), failure.to_string())
}

impl Project {
    pub fn load(root: &Path) -> Result<Self, ProjectError> {
        let root = fs::canonicalize(root).map_err(|failure| io_error(root, failure))?;
        if !root.is_dir() {
            return Err(error(
                &root,
                Span::default(),
                "source root is not a directory",
            ));
        }
        let mut files = Vec::new();
        collect_qli_files(&root, &mut files)?;
        files.sort();

        let mut modules = BTreeMap::new();
        for path in files {
            let name = local_module_name(&root, &path)?;
            let module = parse_source(name.clone(), path, ModuleOrigin::Local)?;
            if modules.insert(name.clone(), module).is_some() {
                return Err(error(
                    &root,
                    Span::default(),
                    format!("duplicate module `{name}`"),
                ));
            }
        }

        let basis_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib/src/basis.qli");
        let basis_ast = parse_module(BUNDLED_BASIS)
            .map_err(|failure| error(&basis_path, failure.span, failure.message))?;
        let basis = SourceModule {
            name: "std::basis".to_owned(),
            path: basis_path,
            source: BUNDLED_BASIS.to_owned(),
            ast: basis_ast,
            imports: BTreeMap::new(),
            origin: ModuleOrigin::Bundled,
        };
        check_declarations(&basis)?;
        modules.insert(basis.name.clone(), basis);

        let mut project = Self { root, modules };
        project.resolve_imports()?;
        project.reject_cycles()?;
        Ok(project)
    }

    pub fn module(&self, name: &str) -> Option<&SourceModule> {
        self.modules.get(name)
    }

    fn resolve_imports(&mut self) -> Result<(), ProjectError> {
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
                    return Err(error(
                        &module.path,
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
    ) -> Result<ResolvedImport, ProjectError> {
        let segments = &use_decl.path;
        if segments.len() < 2 {
            return Err(error(
                &caller.path,
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
            return Err(error(
                &caller.path,
                segments.last().expect("nonempty import path").span,
                format!("sealed module `{source_module}` has no public name `{name}`"),
            ));
        }
        let target = self.modules.get(&source_module).ok_or_else(|| {
            error(
                &caller.path,
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
                error(
                    &caller.path,
                    segments.last().expect("nonempty import path").span,
                    format!("module `{source_module}` has no name `{name}`"),
                )
            })?;
        if !declaration.public {
            return Err(error(
                &caller.path,
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

    fn reject_cycles(&self) -> Result<(), ProjectError> {
        let mut marks = BTreeMap::<&str, u8>::new();
        let mut stack = Vec::<&str>::new();
        for name in self.modules.keys() {
            self.visit(name, &mut marks, &mut stack)?;
        }
        Ok(())
    }

    fn visit<'a>(
        &'a self,
        name: &'a str,
        marks: &mut BTreeMap<&'a str, u8>,
        stack: &mut Vec<&'a str>,
    ) -> Result<(), ProjectError> {
        match marks.get(name).copied() {
            Some(2) => return Ok(()),
            Some(1) => unreachable!("caller diagnoses back edges"),
            _ => {}
        }
        marks.insert(name, 1);
        stack.push(name);
        let module = self.modules.get(name).expect("known module");
        for use_decl in &module.ast.uses {
            let local_name = &use_decl.path.last().expect("parser requires name").text;
            let imported = module.imports.get(local_name).expect("imports resolved");
            if imported.origin == ImportOrigin::Sealed {
                continue;
            }
            let dependency = imported.module.as_str();
            if marks.get(dependency).copied() == Some(1) {
                let start = stack
                    .iter()
                    .position(|item| *item == dependency)
                    .unwrap_or(0);
                let mut cycle = stack[start..].to_vec();
                cycle.push(dependency);
                return Err(error(
                    &module.path,
                    use_decl.span,
                    format!("cyclic import: {}", cycle.join(" -> ")),
                ));
            }
            self.visit(dependency, marks, stack)?;
        }
        stack.pop();
        marks.insert(name, 2);
        Ok(())
    }
}

fn collect_qli_files(directory: &Path, files: &mut Vec<PathBuf>) -> Result<(), ProjectError> {
    let mut entries = fs::read_dir(directory)
        .map_err(|failure| io_error(directory, failure))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|failure| io_error(directory, failure))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let kind = entry
            .file_type()
            .map_err(|failure| io_error(&path, failure))?;
        if kind.is_symlink() {
            return Err(error(
                &path,
                Span::default(),
                "symlinks are not allowed in a source root",
            ));
        }
        if kind.is_dir() {
            collect_qli_files(&path, files)?;
        } else if kind.is_file() && path.extension().is_some_and(|extension| extension == "qli") {
            files.push(path);
        }
    }
    Ok(())
}

fn local_module_name(root: &Path, path: &Path) -> Result<String, ProjectError> {
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
) -> Result<SourceModule, ProjectError> {
    let source = fs::read_to_string(&path).map_err(|failure| io_error(&path, failure))?;
    let ast =
        parse_module(&source).map_err(|failure| error(&path, failure.span, failure.message))?;
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

fn check_declarations(module: &SourceModule) -> Result<(), ProjectError> {
    let mut seen = BTreeSet::new();
    for declaration in &module.ast.decls {
        if !seen.insert(declaration.name.text.as_str()) {
            return Err(error(
                &module.path,
                declaration.name.span,
                format!("duplicate declaration `{}`", declaration.name.text),
            ));
        }
    }
    Ok(())
}

fn sealed_kind(module: &str, name: &str) -> Option<FnKind> {
    match (module, name) {
        ("std::quantum", "init0") => Some(FnKind::Iso),
        ("std::quantum", "h" | "x" | "z" | "t" | "cnot" | "toffoli" | "split" | "join") => {
            Some(FnKind::Unitary)
        }
        ("std::observe", "measure_z" | "reset" | "discard") => Some(FnKind::Observe),
        _ => None,
    }
}
