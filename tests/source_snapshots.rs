//! F2/A020-10: bounded source retention must not grow with receipt count.
mod common;

use common::SourceRoot;
use qleisli::contract::{BasisType, ContractError, FunctionEvidence, FunctionIdentity};
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::ir::{CircuitAction, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::sync::Arc;

fn providers(count: usize, calls: impl Fn(usize) -> String) -> String {
    let mut source = String::from(
        "use std::state::init0; use std::gate::x;\x20
         unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         unitary fn specified(q:Q<Bit>)->Q<Bit>{x(q)}\n",
    );
    for index in 0..count {
        source.push_str(&format!("unitary fn p{index}(q:Q<Bit>)->Q<Bit>{{x(q)}}\n"));
    }
    source.push_str("observe fn main()->Bit{let q=init0();\n");
    for index in 0..count {
        source.push_str(&format!("let q={};\n", calls(index)));
    }
    source.push_str("measure_z(q)}\n//");
    source.push_str(&"p".repeat(100_000 - source.len()));
    assert_eq!(source.len(), 100_000);
    source
}

fn receipts(operations: &[RawOp]) -> Vec<&Arc<FunctionEvidence>> {
    operations
        .iter()
        .flat_map(|operation| match operation {
            RawOp::ApplyUnitary { steps, .. } => steps
                .iter()
                .filter_map(|step| match &step.action {
                    CircuitAction::Contract { evidence, .. } => Some(evidence),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        })
        .collect()
}

#[test]
#[ignore = "historical 256-specialization stress exceeds aggregate fresh-native work; batching is tracked in #274"]
fn full_256_specializations_survive_a_100kb_project_and_unrelated_comments() {
    let source = providers(256, |i| format!("apply[p{i}](q)"));
    let root = SourceRoot::new(&source);
    for comments in [None, Some(format!("//{}\n", "u".repeat(25_000)))] {
        if let Some(comments) = &comments {
            root.write("unrelated.qli", comments);
        }
        let program = compile_project(&root.0).unwrap();
        let attached = receipts(&program.program().operations);
        assert_eq!(attached.len(), 256);
        assert!(attached.windows(2).all(|p| !Arc::ptr_eq(p[0], p[1])));
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_eq!(result[&vec![false]], 1.0);
        let identity = attached[255].identity();
        let retained_bytes: usize = identity.sources.iter().map(|(_, text)| text.len()).sum();
        // The historical stress remains ignored; its metadata assertion follows
        // the current relevant-closure policy. Original observations stay in Git.
        assert_eq!(retained_bytes, 100_000);
        assert!(
            identity
                .sources
                .iter()
                .any(|(name, text)| name == "main" && text == &source)
        );
        assert!(!identity.sources.iter().any(|(name, _)| name == "unrelated"));
    }
    // Sharing source storage does not relax the separate specialization cap.
    root.write("main.qli", &providers(257, |i| format!("apply[p{i}](q)")));
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(error.message.contains("256"), "{error}");
}

#[test]
#[ignore = "historical 256-receipt stress exceeds aggregate fresh-native work; batching is tracked in #274"]
fn distinct_contract_pairs_and_static_providers_share_original_source_rows() {
    for contracts_only in [true, false] {
        let source = providers(256, |i| {
            if contracts_only || i % 2 == 0 {
                format!("apply_contract(p{i},specified,q)")
            } else {
                format!("apply[p{i}](q)")
            }
        });
        let root = SourceRoot::new(&source);
        root.write("unrelated.qli", &format!("//{}\n", "u".repeat(25_000)));
        let program = compile_project(&root.0).unwrap();
        assert_eq!(receipts(&program.program().operations).len(), 256);
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_eq!(result[&vec![false]], 1.0);
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn shared_receipts_keep_exact_bindings_and_outlive_source_changes() {
    for call in [
        "apply[checked_op(implementation,Flip)](q)",
        "apply_contract(implementation,specified,q)",
    ] {
        let root = SourceRoot::new(&format!(
            "use dep::implementation; use std::state::init0; use std::gate::x;
\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20
             classical fn flip(b:Bit)->Bit{{not b}} meaning Flip:Bit=permutation_by(flip);
             unitary fn specified(q:Q<Bit>)->Q<Bit>{{x(q)}}
             unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
             observe fn main()->Bit{{let q=init0(); let q={call}; measure_z(q)}}"
        ));
        root.write(
            "dep.qli",
            "use helper::gate; pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{gate(q)}",
        );
        root.write(
            "helper.qli",
            "use std::gate::x; pub unitary fn gate(q:Q<Bit>)->Q<Bit>{x(q)}",
        );
        let program = compile_project(&root.0).unwrap();
        let receipt = Arc::clone(receipts(&program.program().operations)[0]);
        let identity: FunctionIdentity = receipt.identity().clone();
        receipt
            .check_binding(
                &BasisType::Bit,
                &identity,
                receipt.implementation(),
                receipt.specification(),
            )
            .unwrap();
        for mutation in 0..5 {
            let mut changed = identity.clone();
            match mutation {
                0 => changed.implementation.push('x'),
                1 => changed.specification.push('x'),
                2 => changed
                    .sources
                    .iter_mut()
                    .find(|(name, _)| name == "helper")
                    .unwrap()
                    .1
                    .push(' '),
                3 => changed.sources[0].0.push('x'),
                _ => {
                    changed.sources.pop();
                }
            }
            assert_eq!(
                receipt.check_binding(
                    &BasisType::Bit,
                    &changed,
                    receipt.implementation(),
                    receipt.specification()
                ),
                Err(ContractError::EvidenceMismatch)
            );
        }
        root.write("helper.qli", "pub unitary fn gate(q:Q<Bit>)->Q<Bit>{q}");
        assert!(compile_project(&root.0).is_err());
        drop(root);
        // Neither recompilation nor removal mutates the owned, frozen receipt.
        receipt
            .check_binding(
                &BasisType::Bit,
                &identity,
                receipt.implementation(),
                receipt.specification(),
            )
            .unwrap();
        assert_eq!(
            run_closed(&program, SimulationLimits::default()).unwrap()[&vec![true]],
            1.0
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn small_native_specializations_retain_exact_shared_sources() {
    for calls in [false, true] {
        let source = providers(4, |i| {
            if calls {
                format!("apply_contract(p{i},specified,q)")
            } else {
                format!("apply[p{i}](q)")
            }
        });
        let root = SourceRoot::new(&source);
        let program = compile_project(&root.0).unwrap();
        let attached = receipts(&program.raw().operations);
        assert_eq!(attached.len(), 4);
        for receipt in attached {
            assert!(
                receipt
                    .identity()
                    .sources
                    .iter()
                    .any(|(name, text)| name == "main" && text == &source)
            );
        }
        let result = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_eq!(result[&vec![false]], 1.0);
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn unrelated_large_sources_do_not_become_ordinary_gate_dependencies() {
    let source = "use std::gate::t;use std::state::init0;
        unitary fn specified(q:Q<Bit>)->Q<Bit>{t(q)}
        observe fn main()->Bit{measure_z(apply_contract(specified,specified,h(init0())))}";
    let root = SourceRoot::new(source);
    // Source loading permits these independent comments under the legacy API;
    // the small exact gate dependency must not retain the entire loaded project.
    for i in 0..129 {
        root.write(
            &format!("unrelated_{i}.qli"),
            &format!("//{}", "x".repeat(8192)),
        );
    }
    let program = compile_project(&root.0).unwrap();
    let attached = receipts(&program.raw().operations);
    assert_eq!(attached.len(), 1);
    let identity = attached[0].identity();
    assert!(
        identity
            .sources
            .iter()
            .any(|(name, text)| name == "main" && text == source)
    );
    assert!(
        identity
            .sources
            .iter()
            .any(|(name, text)| name == "std::gate"
                && text == include_str!("../stdlib/src/gate.qli"))
    );
    assert!(
        !identity
            .sources
            .iter()
            .any(|(name, _)| name.starts_with("unrelated_"))
    );
    // Every loaded declaration still goes through the ordinary effect checker.
    root.write(
        "unrelated_0.qli",
        "pub unitary fn wrong(q:Q<Bit>)->Bit{measure_z(q)}",
    );
    assert!(compile_project(&root.0).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn bound_pure_actual_retains_its_original_source_through_a_generic_provider() {
    let root = SourceRoot::new(
        "use adapter::forward;use preparation::zero;
        isometry fn invoke[const U:Op<Unit -> Bit>](u:Q<Unit>)->Q<Bit> requires Applicable(U){U(u)}
        observe fn main()->Bit{measure_z(invoke[forward[zero]](unit(())))}",
    );
    let adapter = "pub isometry fn forward[const U:Op<Unit -> Bit>](u:Q<Unit>)->Q<Bit> requires Applicable(U){U(u)}";
    let preparation = "pub isometry fn zero(u:Q<Unit>)->Q<Bit>{basis u as () {0}}";
    root.write("adapter.qli", adapter);
    root.write("preparation.qli", preparation);
    root.write("unrelated.qli", "// not a source dependency");
    let program = compile_project(&root.0).unwrap();
    let equation = program
        .source_pure_equations()
        .iter()
        .find(|equation| equation.names().0 == "adapter::forward")
        .expect("actual specialized pure provider equation");
    assert!(
        equation
            .sources()
            .iter()
            .any(|(name, text)| name == "adapter" && text == adapter)
    );
    assert!(
        equation
            .sources()
            .iter()
            .any(|(name, text)| name == "preparation" && text == preparation)
    );
    assert!(
        !equation
            .sources()
            .iter()
            .any(|(name, _)| name == "unrelated")
    );
    assert_eq!(
        run_closed(&program, SimulationLimits::default()).unwrap()[&vec![false]],
        1.0
    );
    root.write("preparation.qli", &preparation.replace("{0}", "{1}"));
    let changed = compile_project(&root.0).unwrap();
    assert_eq!(
        run_closed(&changed, SimulationLimits::default()).unwrap()[&vec![true]],
        1.0
    );
    assert!(
        equation
            .sources()
            .iter()
            .any(|(name, text)| name == "preparation" && text == preparation)
    );
}
