//! Existing function contracts across ordinary and selected source adapters.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::contract::{DEFAULT_EXACT_WORK, FunctionEvidence, exact::Budget};
use qleisli::frontend::compile::{
    ElaboratedProgram, Error, ErrorCode, ParsedProgram, RawSourceProposal, compile_project,
};
use qleisli::interchange::{hierarchical, native::Kernel};
use qleisli::ir::{CircuitAction, RawOp, RawProgram};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::process::Command;

const HHH: &str = include_str!(
    "fixtures/authoring_sessions/reference-meaning-v030/attempt-01/contract-hhh/main.qli"
);
const ID: &str = include_str!(
    "fixtures/authoring_sessions/reference-meaning-v030/attempt-01/contract-identity/main.qli"
);
const NEGATIVE_H: &str = include_str!(
    "fixtures/authoring_sessions/reference-meaning-v030/attempt-01/contract-negative-h/main.qli"
);

fn kernel() -> Kernel {
    Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit audited native kernel"))
}

fn work() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}

fn modules(sources: BTreeMap<String, String>) -> ElaboratedProgram {
    ParsedProgram::parse(sources)
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn elaborate(source: &str) -> ElaboratedProgram {
    modules(BTreeMap::from([("main".into(), source.into())]))
}

fn check(source: &ElaboratedProgram) -> Result<ElaboratedProgram, Error> {
    source.check_function_contracts(&kernel(), &mut work())
}

fn lower(source: &ElaboratedProgram) -> Result<RawSourceProposal, Error> {
    source.lower_raw_with_kernel(&kernel(), &mut work())
}

#[test]
fn observing_specialization_refuses_calls_and_retains_unused_obligations() {
    let definitions = "use std::quantum::init0; use std::observe::measure_z;
        fn reference(q: Q<Bit>) -> Bit { measure_z(q) }
        fn implementation(q: Q<Bit>) -> Bit { measure_z(q) }";
    let called = format!(
        "{definitions}
        pub fn main() -> Bit {{ apply_contract(implementation,reference,init0()) }}"
    );
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), called)])).unwrap();
    let error = parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(
        error
            .to_string()
            .contains("observing contract call boundaries")
    );
    let source = elaborate(&format!("{definitions}
        fn unused[const U: Op<Bit>](q: Q<Bit>) -> Bit {{ apply_contract(implementation,reference,q) }}
        pub fn main() -> Bit {{ measure_z(init0()) }}"));
    assert!(source.has_function_contracts());
    let error = check(&source).unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(error.to_string().contains("observing contract obligations"));
    assert!(lower(&source).is_err());
}

fn retained(evidence: &FunctionEvidence, module: &str, original: &str) -> bool {
    evidence
        .identity()
        .sources
        .iter()
        .any(|(name, text)| name == module && text == original)
}

fn receipts(raw: &RawProgram) -> Vec<&FunctionEvidence> {
    raw.operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps),
            _ => None,
        })
        .flatten()
        .filter_map(|step| match &step.action {
            CircuitAction::Contract { evidence, .. } => Some(evidence.as_ref()),
            _ => None,
        })
        .collect()
}

fn selected_zero(source: &str) {
    let proposal = lower(&elaborate(source)).unwrap();
    let accepted = kernel().accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert!((distribution.get(&vec![false]).copied().unwrap_or(0.0) - 1.0).abs() < 1e-12);
    assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-12);
}

#[test]
fn first_hhh_source_runs_unchanged_through_both_adapters_and_cli() {
    let root = SourceRoot::new(HHH);
    let ordinary = compile_project(&root.0).unwrap();
    let distribution = run_closed(&ordinary, SimulationLimits::default()).unwrap();
    assert!((distribution[&vec![false]] - 1.0).abs() < 1e-12);
    selected_zero(HHH);
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["run", "--format=json"])
        .args(["--entry=main::main", "--ir-profile=raw"])
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ))
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let json = String::from_utf8(output.stdout).unwrap();
    let row = json
        .split_once("\"bits\":[false],\"probability\":")
        .expect(&json)
        .1;
    let probability = row.split_once('}').unwrap().0.parse::<f64>().unwrap();
    assert!((probability - 1.0).abs() < 1e-12, "{json}");
    assert!(json.contains("\"source_meaning_verified\":false"), "{json}");
}

#[test]
fn pending_contracts_require_evidence_and_do_not_expand_hierarchy_entry_types() {
    let observed = elaborate(HHH);
    assert!(observed.has_function_contracts());
    assert!(observed.lower_raw().is_err());
    let checked = check(&observed).unwrap();
    assert!(
        checked.lower().is_err(),
        "observing Bit root is not a pure hierarchy entry"
    );
    let pure = HHH.replace("pub observe fn main() -> Bit {\n    measure_z(h(apply_contract(implementation, reference_h, init0())))\n}",
        "pub unitary fn main(q: Q<Bit>) -> Q<Bit> { apply_contract(implementation, reference_h, q) }");
    assert_ne!(pure, HHH);
    let source = elaborate(&pure);
    assert_eq!(source.lower().unwrap_err().code(), "contract");
    assert_eq!(source.lower_raw().unwrap_err().code(), "contract");
    let checked = check(&source).unwrap();
    let proposal = checked.lower().unwrap();
    hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let raw = checked.lower_raw().unwrap();
    raw.validate_source_steps(&kernel().accept(raw.proposal()).unwrap())
        .unwrap();
}

#[test]
fn identity_and_negative_h_fail_exact_equations_in_both_adapters() {
    for source in [ID, NEGATIVE_H] {
        assert!(compile_project(&SourceRoot::new(source).0).is_err());
        let error = check(&elaborate(source)).unwrap_err();
        assert_eq!(error.code(), "contract", "{error}");
        assert!(lower(&elaborate(source)).is_err());
    }
}

#[test]
fn declared_finite_meaning_keeps_its_request_on_both_adapters() {
    let source = "use std::quantum::{init0,x}; use std::observe::measure_z;
        classical fn flip(b: Bit) -> Bit { not b }
        meaning X: Bit = permutation_by(flip);
        unitary fn implementation(q: Q<Bit>) -> Q<Bit> { x(q) }
        pub observe fn main() -> Bit { measure_z(x(apply_contract(implementation,X,init0()))) }";
    let ordinary = compile_project(&SourceRoot::new(source).0).unwrap();
    assert!(
        (run_closed(&ordinary, SimulationLimits::default()).unwrap()[&vec![false]] - 1.0).abs()
            < 1e-12
    );
    selected_zero(source);
    let wrong = source.replace("{ x(q) }", "{ q }");
    assert!(compile_project(&SourceRoot::new(&wrong).0).is_err());
    assert_eq!(check(&elaborate(&wrong)).unwrap_err().code(), "contract");
}

#[test]
fn unused_and_zero_count_contracts_are_not_erased() {
    let definitions = "use std::quantum::{init0,h}; use std::observe::measure_z;
        unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
        unitary fn specified(q: Q<Bit>) -> Q<Bit> { h(q) }";
    for body in [
        "unitary fn unused(q: Q<Bit>) -> Q<Bit> { apply_contract(identity,specified,q) }
         pub observe fn main() -> Bit { measure_z(init0()) }",
        "pub observe fn main() -> Bit { let q=init0();
         let q=qfor static i in 0..0 carry q=q { yield apply_contract(identity,specified,q); };
         measure_z(q) }",
    ] {
        let source = elaborate(&format!("{definitions} {body}"));
        assert!(source.has_function_contracts());
        assert_eq!(check(&source).unwrap_err().code(), "contract");
    }
}

#[test]
fn unused_generic_body_keeps_its_closed_function_contract_in_both_adapters() {
    let source = "use std::quantum::{init0,h}; use std::observe::measure_z;
        unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
        unitary fn specified(q: Q<Bit>) -> Q<Bit> { h(q) }
        unitary fn unused[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit> {
            apply_contract(identity,specified,q)
        }
        pub observe fn main() -> Bit { measure_z(init0()) }";
    assert_eq!(
        compile_project(&SourceRoot::new(source).0)
            .unwrap_err()
            .code,
        ErrorCode::Contract
    );
    let selected = elaborate(source);
    assert!(selected.has_function_contracts());
    assert_eq!(check(&selected).unwrap_err().code(), "contract");
}

#[test]
fn nested_contracts_keep_their_independent_dependencies() {
    let source = HHH.replace("pub observe fn main()", "unitary fn nested(q: Q<Bit>) -> Q<Bit> { apply_contract(implementation,reference_h,q) }\npub observe fn main()")
        .replace("measure_z(h(apply_contract(implementation, reference_h, init0())))",
            "measure_z(h(apply_contract(nested,reference_h,init0())))");
    selected_zero(&source);
    let wrong = source.replace("{ h(h(h(q))) }", "{ q }");
    assert_eq!(check(&elaborate(&wrong)).unwrap_err().code(), "contract");
}

#[test]
fn absent_kernel_exhausted_budget_and_wrong_tree_fail_closed() {
    let source = elaborate(HHH);
    let root = SourceRoot::new("");
    assert!(
        source
            .check_function_contracts(&Kernel::new(root.0.join("absent-kernel")), &mut work())
            .is_err()
    );
    assert_eq!(
        source
            .check_function_contracts(&kernel(), &mut Budget::new(1))
            .unwrap_err()
            .code(),
        "limit"
    );
    let wrong = "unitary fn implementation(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> { q }
        unitary fn specified(q: Q<Bit>) -> Q<Bit> { q }
        pub unitary fn main(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> { apply_contract(implementation,specified,q) }";
    assert!(ParsedProgram::parse(BTreeMap::from([("main".into(), wrong.into())])).is_err());
    assert!(compile_project(&SourceRoot::new(wrong).0).is_err());
}

#[test]
fn changed_reference_dependency_is_rechecked_from_new_sources() {
    let main = HHH.replace(
        "unitary fn reference_h(q: Q<Bit>) -> Q<Bit> { h(q) }",
        "use dependency::reference_h;",
    );
    let dependency =
        "use std::quantum::h; pub unitary fn reference_h(q: Q<Bit>) -> Q<Bit> { h(q) }";
    let make = |dep: &str| {
        modules(BTreeMap::from([
            ("main".into(), main.clone()),
            ("dependency".into(), dep.into()),
        ]))
    };
    let original = lower(&make(dependency)).unwrap();
    let accepted = kernel().accept(original.proposal()).unwrap();
    original.validate_source_steps(&accepted).unwrap();
    assert!(
        receipts(accepted.raw())
            .iter()
            .any(|e| retained(e, "dependency", dependency))
    );
    let changed = dependency.replace("{ h(q) }", "{ q }");
    assert_eq!(check(&make(&changed)).unwrap_err().code(), "contract");
}

#[test]
fn receipt_sources_and_actual_emitted_step_cannot_be_substituted() {
    let proposal = lower(&elaborate(HHH)).unwrap();
    let accepted = kernel().accept(proposal.proposal()).unwrap();
    let all = receipts(accepted.raw());
    assert_eq!(all.len(), 1);
    let evidence = all[0];
    assert!(retained(evidence, "main", HHH));
    let mut identity = evidence.identity().clone();
    identity
        .sources
        .iter_mut()
        .find(|(name, _)| name == "main")
        .unwrap()
        .1
        .push(' ');
    assert!(
        evidence
            .check_binding(
                evidence.signature(),
                &identity,
                evidence.implementation(),
                evidence.specification()
            )
            .is_err()
    );
    let mut changed = accepted.raw().clone();
    let mut count = 0;
    for op in &mut changed.operations {
        if let RawOp::ApplyUnitary { steps, .. } = op {
            for step in steps {
                if let CircuitAction::Contract { adjoint, .. } = &mut step.action {
                    *adjoint = !*adjoint;
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 1);
    // H is self-adjoint, so validity can pass; exact source attachment must not.
    let changed = kernel().accept_raw(changed).unwrap();
    assert!(proposal.validate_source_steps(&changed).is_err());
}

#[test]
fn equal_matrix_receipt_cannot_replace_the_original_implementation_snapshot() {
    let proposal = lower(&elaborate(HHH)).unwrap();
    let accepted = kernel().accept(proposal.proposal()).unwrap();
    let original = receipts(accepted.raw())[0];
    // Identity metadata is deliberately unchanged: neither names nor equality
    // of matrices proves that this H/H receipt binds the original HHH body.
    let replacement = FunctionEvidence::check(
        original.signature().clone(),
        original.specification().clone(),
        original.specification().clone(),
        original.identity().clone(),
        &mut work(),
    )
    .unwrap();
    assert_eq!(replacement.meaning(), original.meaning());
    assert_ne!(replacement.implementation(), original.implementation());
    let replacement = std::sync::Arc::new(replacement);
    let mut changed = accepted.raw().clone();
    let mut count = 0;
    for operation in &mut changed.operations {
        if let RawOp::ApplyUnitary { steps, .. } = operation {
            for step in steps {
                if let CircuitAction::Contract { evidence, .. } = &mut step.action {
                    *evidence = replacement.clone();
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 1);
    let changed = kernel().accept_raw(changed).unwrap();
    // This public gate enforces immutable artifact identity before replay.
    // The inner receipt/body comparison has a separate internal regression.
    assert!(proposal.validate_source_steps(&changed).is_err());
}
