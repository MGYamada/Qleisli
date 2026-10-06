use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use qleisli::frontend::compile::{ErrorCode, check_project};
use qleisli::frontend::project::{ImportOrigin, ModuleOrigin, Project, ProjectError};

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
        fs::write(path.join("Qargo.toml"), include_str!("Qargo.toml")).unwrap();
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

    fn write_import_chain(&self, count: usize, last_dependency: Option<usize>) {
        for index in 0..count {
            let dependency = if index + 1 < count {
                Some(index + 1)
            } else {
                last_dependency
            };
            let import = dependency
                .map_or_else(String::new, |next| format!("use m{next:04}::f{next:04};\n"));
            self.write(
                &format!("m{index:04}.qli"),
                &format!("// π\n{import}pub classical fn f{index:04}(x: Bit) -> Bit {{ x }}\n"),
            );
        }
    }
}

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn load_on_small_stack(root: &Path) -> Result<Project, ProjectError> {
    let root = root.to_owned();
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(move || Project::load(&root))
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn bell_module_and_bundled_imports_resolve() {
    let root = TempRoot::new();
    root.write(
        "bell.qli",
        "pub iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> { basis q as x { (x, x) } }",
    );
    root.write(
        "main.qli",
        "use bell::entangle;\nuse std::quantum::h;\nuse std::quantum::init0;\nuse std::basis::xor2;\nuse std::observe::measure_z;\nobserve fn main() -> Bit { measure_z(init0()) }",
    );
    root.write(
        "nested/helper.qli",
        "pub classical fn id(x: Bit) -> Bit { x }",
    );

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
    root.write("lib.qli", "classical fn hidden(x: Bit) -> Bit { x }");
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

    root.write("present.qli", "pub classical fn item(x: Bit) -> Bit { x }");
    root.write("main.qli", "use present::other;");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("has no name `other`"), "{error}");
}

#[test]
fn import_only_cycles_load_but_call_cycles_and_name_collisions_reject() {
    let root = TempRoot::new();
    root.write("a.qli", "use b::g; pub classical fn f(x: Bit) -> Bit { x }");
    root.write("b.qli", "use a::f; pub classical fn g(x: Bit) -> Bit { x }");
    let project = Project::load(root.path()).unwrap();
    assert_eq!(project.module("a").unwrap().imports["g"].module, "b");
    assert_eq!(project.module("b").unwrap().imports["f"].module, "a");

    root.write(
        "a.qli",
        "use b::g; pub classical fn f(x: Bit) -> Bit { g(x) }",
    );
    let cyclic = "use a::f; pub classical fn g(x: Bit) -> Bit { f(x) }";
    root.write("b.qli", cyclic);
    Project::load(root.path()).unwrap();
    let error = check_project(root.path()).unwrap_err();
    assert_eq!(error.code, ErrorCode::RecursiveCall, "{error}");
    assert!(error.path.ends_with("b.qli"), "{error}");
    assert_eq!(&cyclic[error.span.start..error.span.end], "f");

    root.write("b.qli", "pub classical fn g(x: Bit) -> Bit { x }");
    root.write("a.qli", "use b::g; classical fn g(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("collides"), "{error}");
}

#[test]
fn tiny_import_only_cycle_loads_on_a_small_stack() {
    let root = TempRoot::new();
    root.write_import_chain(3, Some(1));
    let project = load_on_small_stack(root.path()).unwrap();
    assert_eq!(
        project.module("m0002").unwrap().imports["f0001"].module,
        "m0001"
    );
}

#[test]
fn long_acyclic_import_chain_loads_on_a_small_stack() {
    let root = TempRoot::new();
    // This depth overflowed the recursive import DFS on a 2 MiB Rust thread.
    let count = 3_000;
    root.write_import_chain(count, None);
    let project = load_on_small_stack(root.path()).unwrap();
    assert_eq!(
        project
            .modules
            .values()
            .filter(|module| module.origin == ModuleOrigin::Local)
            .count(),
        count
    );
    assert_eq!(
        project.module("m0000").unwrap().imports["f0001"].module,
        "m0001"
    );
    assert!(project.module("m2999").unwrap().imports.is_empty());
}

#[test]
fn deep_import_only_cycle_loads_on_a_small_stack() {
    let root = TempRoot::new();
    let count = 3_000;
    let cycle_start = 1_200;
    root.write_import_chain(count, Some(cycle_start));
    let project = load_on_small_stack(root.path()).unwrap();
    assert_eq!(
        project
            .modules
            .values()
            .filter(|module| module.origin == ModuleOrigin::Local)
            .count(),
        count
    );
    let last = project.module("m2999").unwrap();
    let back_edge = &last.imports["f1200"];
    assert_eq!(back_edge.module, format!("m{cycle_start:04}"));
    assert_eq!(back_edge.name, format!("f{cycle_start:04}"));
    assert_eq!(back_edge.origin, ImportOrigin::Local);
    assert_eq!(back_edge.span.start, "// π\n".len());
    assert_eq!(
        &last.source[back_edge.span.start..back_edge.span.end],
        "use m1200::f1200;"
    );
}

#[test]
fn converging_import_paths_do_not_report_a_cycle() {
    let root = TempRoot::new();
    root.write("a.qli", "use b::left; use c::right; use d::shared;");
    root.write(
        "b.qli",
        "use d::shared; pub classical fn left(x: Bit) -> Bit { x }",
    );
    root.write(
        "c.qli",
        "use d::shared; pub classical fn right(x: Bit) -> Bit { x }",
    );
    root.write("d.qli", "pub classical fn shared(x: Bit) -> Bit { x }");
    let project = Project::load(root.path()).unwrap();
    for name in ["a", "b", "c"] {
        assert_eq!(project.module(name).unwrap().imports["shared"].module, "d");
    }
}

#[test]
fn std_prefix_and_invalid_module_names_cannot_shadow_bundled_modules() {
    let root = TempRoot::new();
    root.write("std/quantum.qli", "pub classical fn h(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("reserved"), "{error}");

    fs::remove_dir_all(root.path().join("std")).unwrap();
    root.write("bad-name.qli", "classical fn f(x: Bit) -> Bit { x }");
    let error = Project::load(root.path()).unwrap_err();
    assert!(
        error.message.contains("invalid module path component"),
        "{error}"
    );
}

#[test]
fn reserved_word_cannot_name_a_local_module() {
    let root = TempRoot::new();
    root.write("if.qli", "pub classical fn item(x: Bit) -> Bit { x }");
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
fn semantic_stdlib_modules_are_bundled_source_with_private_helpers() {
    let root = TempRoot::new();
    root.write("main.qli", "use std::reflection::reflect_uniform2;");
    let project = Project::load(root.path()).unwrap();
    assert_eq!(
        project.module("main").unwrap().imports["reflect_uniform2"].origin,
        ImportOrigin::Bundled
    );
    let reflection = project.module("std::reflection").unwrap();
    assert_eq!(reflection.origin, ModuleOrigin::Bundled);
    assert!(!reflection.ast.decls.is_empty());
    assert_eq!(
        reflection.imports["hadamard2"].origin,
        ImportOrigin::Bundled
    );
    assert_eq!(reflection.imports["hadamard2"].module, "std::transform");

    root.write("main.qli", "use std::reflection::nonzero2;");
    let error = Project::load(root.path()).unwrap_err();
    assert!(error.message.contains("not public"), "{error}");
}

#[test]
fn semantic_stdlib_public_paths_resolve_without_retired_namespace_aliases() {
    let root = TempRoot::new();
    for (module, names) in [
        ("transform", &["hadamard2", "qft2", "qft3"][..]),
        ("reflection", &["reflect_uniform2"][..]),
        ("measurement", &["measure_x", "measure_z2", "parity_zz"][..]),
    ] {
        use std::fmt::Write;
        let mut source = String::new();
        for name in names {
            write!(&mut source, "use std::{module}::{name};").unwrap();
        }
        root.write("main.qli", &source);
        let project = Project::load(root.path()).unwrap();
        for name in names {
            let import = &project.module("main").unwrap().imports[*name];
            assert_eq!(
                import.origin,
                ImportOrigin::Bundled,
                "std::{module}::{name}"
            );
            assert_eq!(import.module, format!("std::{module}"));
        }
        assert!(project.module("std::transforms").is_none());
        assert!(project.module("std::routines").is_none());
    }
    for (module, names) in [
        ("transforms", &["qft2", "qft3"][..]),
        (
            "routines",
            &[
                "hadamard2",
                "reflect_uniform2",
                "measure_x",
                "measure_z2",
                "parity_zz",
            ][..],
        ),
        ("arithmetic", &["increment2", "add2", "mul2_mod15"][..]),
    ] {
        for name in names {
            root.write("main.qli", &format!("use std::{module}::{name};"));
            assert!(
                Project::load(root.path()).is_err(),
                "retired stdlib alias resolved: std::{module}::{name}"
            );
        }
    }
}
