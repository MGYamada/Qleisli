mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{compile_project, compile_project_with_policy};
use qleisli::frontend::project::{ModuleOrigin, Project, SourcePolicy, read_source_file};

#[test]
fn source_boundaries_count_utf8_bytes_before_decoding() {
    let root = SourceRoot::new("// 日本語\n");
    let path = root.0.join("main.qli");
    let bytes = std::fs::metadata(&path).unwrap().len();
    let policy = |n| SourcePolicy::Bounded {
        source_bytes: n,
        project_bytes: 1000,
    };
    assert!(read_source_file(&path, policy(bytes)).is_ok());
    let error = read_source_file(&path, policy(bytes - 1)).unwrap_err();
    assert_eq!(error.code, "limit");
    assert!(error.primary.is_none());
    std::fs::write(&path, [0xff_u8; 4]).unwrap();
    assert_eq!(
        read_source_file(&path, policy(3)).unwrap_err().code,
        "limit"
    );
    assert_eq!(
        read_source_file(&path, policy(4)).unwrap_err().code,
        "project"
    );
}

#[test]
fn aggregate_includes_many_files_and_bundled_sources() {
    let root = SourceRoot::new("observe fn main() -> CBit { true }");
    for i in 0..20 {
        root.write(&format!("m{i}.qli"), "// a small module\n");
    }
    let loaded = Project::load(&root.0).unwrap();
    let total = loaded.modules.values().map(|m| m.source.len() as u64).sum();
    assert!(
        loaded
            .modules
            .values()
            .any(|m| m.origin == ModuleOrigin::Bundled)
    );
    let policy = |n| SourcePolicy::Bounded {
        source_bytes: 1 << 20,
        project_bytes: n,
    };
    assert!(Project::load_with_policy(&root.0, policy(total)).is_ok());
    let error = Project::load_with_policy(&root.0, policy(total - 1)).unwrap_err();
    assert_eq!(error.code, "limit");
    assert!(error.message.contains("bundled"));
    assert!(error.primary.is_none());
}

#[test]
fn old_host_api_and_explicit_legacy_policy_keep_large_sources() {
    let source = format!(
        "observe fn main() -> CBit {{ false }}\n//{}",
        "x".repeat(1 << 20)
    );
    let root = SourceRoot::new(&source);
    assert_eq!(
        compile_project_with_policy(&root.0, SourcePolicy::default())
            .unwrap_err()
            .code,
        "limit"
    );
    assert!(compile_project(&root.0).is_ok());
    assert!(compile_project_with_policy(&root.0, SourcePolicy::Legacy).is_ok());
    assert!(
        compile_project_with_policy(
            &root.0,
            SourcePolicy::Bounded {
                source_bytes: 2 << 20,
                project_bytes: 16 << 20
            }
        )
        .is_ok()
    );
}

#[test]
fn zero_and_overflow_policies_fail_explicitly() {
    let root = SourceRoot::new("");
    for policy in [
        SourcePolicy::Bounded {
            source_bytes: 0,
            project_bytes: 10,
        },
        SourcePolicy::Bounded {
            source_bytes: 10,
            project_bytes: 0,
        },
        SourcePolicy::Bounded {
            source_bytes: u64::MAX,
            project_bytes: u64::MAX,
        },
    ] {
        assert_eq!(
            read_source_file(&root.0.join("main.qli"), policy)
                .unwrap_err()
                .code,
            "limit"
        );
    }
}
