use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use qleisli_core::frontend::project::{ImportOrigin, ModuleOrigin, Project};

static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

struct TempRoot {
    path: PathBuf,
}

impl TempRoot {
    fn new() -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "qleisli-project-{}-{timestamp}-{}",
            std::process::id(),
            NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self { path }
    }

    fn write(&self, relative: &str, source: &str) {
        let path = self.path.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn bell_module_and_bundled_imports_resolve() {
    let root = TempRoot::new();
    root.write(
        "bell.qli",
        "pub iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> { do x <- q; pure (x, x) }",
    );
    root.write(
        "main.qli",
        "use bell::entangle;\nuse std::quantum::h;\nuse std::quantum::init0;\nuse std::basis::xor2;\nuse std::observe::measure_z;\nobserve fn main() -> CBit { measure_z(init0()) }",
    );
    root.write("nested/helper.qli", "pub basis fn id(x: Bit) -> Bit { x }");

    let project = Project::load(root.path()).unwrap();
    assert!(project.module("nested::helper").is_some());
    let main = project.module("main").unwrap();
    assert_eq!(main.origin, ModuleOrigin::Local);
    assert_eq!(main.imports["entangle"].module, "bell");
    assert_eq!(main.imports["entangle"].origin, ImportOrigin::Local);
    assert_eq!(main.imports["h"].origin, ImportOrigin::Sealed);
    assert_eq!(main.imports["xor2"].origin, ImportOrigin::Bundled);
    assert_eq!(main.imports["measure_z"].origin, ImportOrigin::Sealed);
    let basis = project.module("std::basis").unwrap();
    assert_eq!(basis.origin, ModuleOrigin::Bundled);
    assert_eq!(basis.ast.decls.len(), 2);
    assert!(project.module("std::quantum").is_none());
}

#[test]
fn nonpublic_import_reports_calling_file_and_utf8_byte_span() {
    let root = TempRoot::new();
    root.write("lib.qli", "basis fn hidden(x: Bit) -> Bit { x }");
    let source = "// π\nuse lib::hidden;\n";
    root.write("main.qli", source);
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.path.ends_with("main.qli"));
    assert!(error.message.contains("not public"), "{error}");
    let start = source.find("hidden").unwrap();
    assert_eq!(error.span.start, start);
    assert_eq!(error.span.end, start + "hidden".len());
}

#[test]
fn missing_module_and_name_are_distinct_errors() {
    let root = TempRoot::new();
    root.write("main.qli", "use absent::item;");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("missing module `absent`"), "{error}");

    root.write("present.qli", "pub basis fn item(x: Bit) -> Bit { x }");
    root.write("main.qli", "use present::other;");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("has no name `other`"), "{error}");
}

#[test]
fn import_cycles_and_name_collisions_are_rejected() {
    let root = TempRoot::new();
    root.write("a.qli", "use b::g; pub basis fn f(x: Bit) -> Bit { x }");
    root.write("b.qli", "use a::f; pub basis fn g(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("cyclic import"), "{error}");
    assert!(error.path.ends_with("b.qli"));

    root.write("b.qli", "pub basis fn g(x: Bit) -> Bit { x }");
    root.write("a.qli", "use b::g; basis fn g(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("collides"), "{error}");
}

#[test]
fn std_prefix_and_invalid_module_names_cannot_shadow_bundled_modules() {
    let root = TempRoot::new();
    root.write("std/quantum.qli", "pub basis fn h(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("reserved"), "{error}");

    fs::remove_dir_all(root.path().join("std")).unwrap();
    root.write("bad-name.qli", "basis fn f(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(
        error.message.contains("invalid module path component"),
        "{error}"
    );
}

#[test]
fn reserved_word_cannot_name_a_local_module() {
    let root = TempRoot::new();
    root.write("if.qli", "pub basis fn item(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.path.ends_with("if.qli"));
    assert!(error.message.contains("invalid module path component"));
}

#[test]
fn unknown_sealed_name_is_not_reinterpreted_as_user_code() {
    let root = TempRoot::new();
    root.write("main.qli", "use std::quantum::untrusted_gate;");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("sealed module"), "{error}");
}

#[test]
fn algorithm_routines_are_bundled_source_with_private_helpers() {
    let root = TempRoot::new();
    root.write("main.qli", "use std::routines::reflect_uniform2;");
    let project = Project::load(root.path()).unwrap();
    assert_eq!(
        project.module("main").unwrap().imports["reflect_uniform2"].origin,
        ImportOrigin::Bundled
    );
    let routines = project.module("std::routines").unwrap();
    assert_eq!(routines.origin, ModuleOrigin::Bundled);
    assert!(!routines.ast.decls.is_empty());
    assert_eq!(routines.imports["h"].origin, ImportOrigin::Sealed);

    root.write("main.qli", "use std::routines::nonzero2;");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("not public"), "{error}");
}
