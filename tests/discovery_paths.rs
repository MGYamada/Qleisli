//! Documentation discovery must never become execution or native acceptance.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use std::process::{Command, Output};

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(args)
        .env("QLEISLI_KERNEL", "/nonexistent/discovery-checker")
        .env("QLEISLI_HIERARCHY_KERNEL", "/nonexistent/discovery-checker")
        .output()
        .unwrap()
}

#[test]
fn standalone_help_discovers_native_tools_without_project_or_checker() {
    for args in [&["--help"][..], &["help"][..]] {
        let output = run(args);
        assert!(output.status.success());
        assert!(output.stderr.is_empty());
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("qleisli help ecosystem"));
        for role in [
            "QLT: mathematical tests",
            "QDB: failure/obligation navigation",
            "QCP: circuit/resource profiling",
        ] {
            assert!(text.contains(role));
        }
        assert!(text.contains("planned, not executable"));
    }
}

#[test]
fn ecosystem_help_is_the_single_canonical_chapter() {
    let output = run(&["help", "ecosystem"]);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    assert_eq!(
        output.stdout,
        std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/docs/src/reference/discovery.md"
        ))
        .unwrap()
    );
}

#[test]
fn unavailable_tools_and_invalid_help_keep_usage_failures_and_discovery() {
    for args in [
        vec!["qlt"],
        vec!["qdb"],
        vec!["qcp"],
        vec!["qlippy"],
        vec!["help", "unknown"],
        vec!["--help", "--format=json"],
        vec!["help", "ecosystem", "--format=json"],
        vec![
            "help",
            "ecosystem",
            "--entry=main::f",
            "--module=main=/nonexistent/source",
        ],
        vec!["sized", "qlt"],
        vec!["interop", "qlt"],
    ] {
        let output = run(&args);
        assert_eq!(output.status.code(), Some(2), "{args:?}");
        let text = String::from_utf8([output.stdout, output.stderr].concat()).unwrap();
        assert!(text.contains("qleisli help ecosystem"), "{args:?}: {text}");
        assert!(!text.contains("could not start"));
        if args.contains(&"--format=json") || args[0] == "interop" {
            assert!(text.contains("\"code\":\"usage\""), "{text}");
            assert!(text.contains("\"outcome\":\"error\""), "{text}");
        }
    }
}
