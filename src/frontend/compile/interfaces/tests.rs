//! Small private closure experiments, without generic production admission.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::project::{ModuleOrigin, SourceModule};

const FIRST: &str = "tests/fixtures/authoring_sessions/interface-naturals-v030";

fn project(text: String) -> Project {
    let ast = crate::frontend::parser::parse_module(&text).expect("ordinary source translation");
    Project {
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: text,
                ast,
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    }
}

fn first(case: &str) -> Project {
    let text = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(FIRST)
            .join("translations")
            .join(case)
            .join("main.qli"),
    )
    .expect("retained separate translation");
    project(text)
}

fn bindings(compiler: &Compiler<'_>, key: Key, n: u32) -> BTreeMap<BinderKey, u32> {
    let formal = &compiler.source.interfaces[&key].statics[0];
    assert!(matches!(formal.kind, StaticKind::Natural));
    BTreeMap::from([(formal.key.clone(), n)])
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_signature_u32_checks_differ_from_checked_helper_template_arithmetic() {
    for (case, refuses) in [("ordinary", true), ("helper", false)] {
        let project = first(case);
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let key = compiler.source.resolution.qualified("main::keep").unwrap();
        let span = compiler.declarations[&key].span;
        for n in [0, 1, 2_147_483_648] {
            let values = bindings(&compiler, key, n);
            let result = compiler.close_instance_interface(key, BTreeMap::new(), values, span);
            if refuses && n == 2_147_483_648 {
                let error = match result {
                    Ok(_) => panic!("normalized zero erased the original signature overflow"),
                    Err(error) => error,
                };
                assert_eq!(error.code, ErrorCode::Limit);
                assert!(error.message.contains("concrete natural arithmetic"));
                let source = &project.modules["main"].source;
                assert_eq!(&source[error.span.start..error.span.end], "(n+n)");
            } else {
                let closed = result.expect("original signature discharged");
                assert!(matches!(closed.parameters[0].kind, Kind::Bits(0)));
                assert!(matches!(closed.result.kind, Kind::Bits(0)));
            }
        }
        // The private experiment must not relax whole-source profile admission.
        let error = process_loaded_project(Path::new("main.qli"), &project, false).unwrap_err();
        assert_eq!(error.code, ErrorCode::Unsupported);
        assert!(error.message.contains("static Nat parameters"));
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_signature_paths_bind_runtime_quantum_trees_and_both_operation_ports() {
    let project = project(
        "isometry fn keep[const n:Nat,const U:Op<(Bits<n>,Unit) -> Bits<n>>]\n\
         (q:Q<(Bits<n>,Unit)>)->Q<Bits<n>> requires Applicable(U){U(q)}"
            .into(),
    );
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler.source.resolution.qualified("main::keep").unwrap();
    let span = compiler.declarations[&key].span;
    let values = bindings(&compiler, key, 0);
    let mut closed = compiler
        .close_instance_interface(key, BTreeMap::new(), values, span)
        .unwrap();
    assert_eq!(compiler.interface_naturals[&key].roots.len(), 4);
    closed.result =
        super::super::super::types::Type::quantum(super::super::super::types::Type::unit());
    assert!(
        compiler
            .validate_interface_naturals(key, &closed, span)
            .unwrap_err()
            .message
            .contains("different constructor")
    );
    closed.result =
        super::super::super::types::Type::quantum(super::super::super::types::Type::bits(0));
    let operation = closed.operations.values_mut().next().unwrap();
    operation.codomain = Some(super::super::super::types::Type::quantum(
        super::super::super::types::Type::bits(1),
    ));
    assert!(
        compiler
            .validate_interface_naturals(key, &closed, span)
            .unwrap_err()
            .message
            .contains("differs from normalized closure")
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn interface_validation_refuses_missing_originals_and_preserves_consumed_work() {
    let project = first("helper");
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler.source.resolution.qualified("main::keep").unwrap();
    let span = compiler.declarations[&key].span;
    let values = bindings(&compiler, key, 0);
    let closed = compiler
        .close_instance_interface(key, BTreeMap::new(), values, span)
        .unwrap();
    compiler.work = MAX_WORK - 2;
    assert_eq!(
        compiler
            .validate_interface_naturals(key, &closed, span)
            .unwrap_err()
            .code,
        ErrorCode::Limit
    );
    assert!(compiler.work >= MAX_WORK - 2);
    compiler.work = 0;
    compiler.interface_naturals.remove(&key);
    assert!(
        compiler
            .validate_interface_naturals(key, &closed, span)
            .unwrap_err()
            .message
            .contains("missing original")
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn closed_runtime_signature_checks_capacity_before_proposal_materialization() {
    for (size, helper, refuses) in [
        ("(3000000000+3000000000)-3000000000-3000000000", "", true),
        (
            "cancel[3000000000]()",
            "static fn cancel[const n: Nat]() -> Nat { (n+n)-n-n }\n",
            false,
        ),
    ] {
        let project = project(format!(
            "use std::classical::empty_bits;\n{helper}\
             unitary fn keep(b: Bits<{size}>) -> Bits<0> {{ b }}\n\
             unitary fn main() -> Unit {{ let _ = keep(empty_bits()); () }}\n"
        ));
        let result = process_loaded_project(Path::new("main.qli"), &project, true);
        if refuses {
            let error = result.unwrap_err();
            assert_eq!(error.code, ErrorCode::Limit);
            assert!(error.message.contains("concrete natural arithmetic"));
            assert_eq!(
                &project.modules["main"].source[error.span.start..error.span.end],
                "(3000000000+3000000000)"
            );
        } else {
            assert!(
                result
                    .expect("checked helper keeps its exact zero result")
                    .is_some()
            );
        }
    }
}
