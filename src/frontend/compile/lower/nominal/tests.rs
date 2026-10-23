//! Raw-only producer probes: no native request or accepted handle is constructed.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

mod records;
use crate::frontend::compile::lower::call_state_tests::untrusted_compiler;
use crate::frontend::project::{ModuleOrigin, ProjectEdition, SourceModule};

// Exact retained first source from the ordinary-runtime authoring session.
const FIRST: &str = r#"use std::state::init0;

enum Tri { A, B, C }

fn choose(b: Bit) -> Tri {
    if b { Tri::B } else { Tri::C }
}

classical fn is_b(t: Tri) -> Bit {
    match t {
        Tri::A => 0,
        Tri::B => 1,
        Tri::C => 0,
    }
}

pub observe fn main() -> Bit {
    let b = measure_z(h(init0()));
    is_b(choose(b))
}
"#;
const STATE: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/stdlib/src/state.qli"));

fn source_module(name: &str, text: &str, origin: ModuleOrigin) -> SourceModule {
    SourceModule {
        name: name.into(),
        path: PathBuf::from(format!("{name}.qli")),
        source: text.into(),
        ast: crate::frontend::parser::parse_module(text).expect("probe parses"),
        imports: BTreeMap::new(),
        origin,
    }
}

fn project(text: &str) -> Project {
    Project {
        edition_context: ProjectEdition::Explicit(crate::edition::Edition::E2026),
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([
            (
                "main".into(),
                source_module("main", text, ModuleOrigin::Local),
            ),
            (
                "std::state".into(),
                source_module("std::state", STATE, ModuleOrigin::Bundled),
            ),
        ]),
    }
}

fn lowerer<'c, 'p>(compiler: &'c mut Compiler<'p>) -> Lowerer<'c, 'p> {
    Lowerer {
        compiler,
        raw: RawState::new(),
        operation_sources: BTreeMap::new(),
        instrument_calls: Vec::new(),
        tuple_binding_origins: vec![BTreeMap::new()],
        access_updates: vec![BTreeSet::new()],
        effect: Effect::Unitary,
        contract_effect: Effect::Unitary,
        effect_source: None,
        depth: 0,
        bindings: BTreeMap::new(),
    }
}

fn raw_main(project: &Project) -> (Value, RawState<u32>, Effect) {
    let mut compiler = untrusted_compiler(project);
    let key = compiler.source.resolution.qualified("main::main").unwrap();
    let mut lower = lowerer(&mut compiler);
    let value = lower
        .call_user(&key, Vec::new(), None)
        .expect("untrusted producer");
    assert!(lower.compiler.checked.is_empty());
    assert!(lower.compiler.function_evidence.is_empty());
    assert!(lower.compiler.instrument_evidence.is_empty());
    assert!(lower.instrument_calls.is_empty());
    (value, lower.raw, lower.effect)
}

// This is a bounded classical observation of an untrusted proposal, not a
// quantum simulator or checker. The measured outcome is supplied explicitly;
// no probability, source-preservation theorem or accepted execution is claimed.
fn classical_history(ops: &[RawOp], outcome: bool, values: &mut BTreeMap<ClassicalId, bool>) {
    for op in ops {
        match op {
            RawOp::ClassicalConst { value, output } => {
                assert!(values.insert(*output, *value).is_none());
            }
            RawOp::ClassicalNot { input, output } => {
                let value = !values[input];
                assert!(values.insert(*output, value).is_none());
            }
            RawOp::ClassicalXor {
                left,
                right,
                output,
            } => {
                let value = values[left] ^ values[right];
                assert!(values.insert(*output, value).is_none());
            }
            RawOp::ClassicalAnd {
                left,
                right,
                output,
            } => {
                let value = values[left] && values[right];
                assert!(values.insert(*output, value).is_none());
            }
            RawOp::MeasureZ { output, .. } => {
                assert!(values.insert(*output, outcome).is_none());
            }
            RawOp::ClassicalBranch {
                condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
            } => {
                assert!(quantum_phis.is_empty());
                let choice = values[condition];
                let mut selected = values.clone();
                classical_history(
                    if choice { then_ops } else { else_ops },
                    outcome,
                    &mut selected,
                );
                // Every source is read before any destination is introduced.
                let outputs: Vec<_> = classical_phis
                    .iter()
                    .map(|phi| {
                        (
                            phi.output,
                            selected[&if choice { phi.then_id } else { phi.else_id }],
                        )
                    })
                    .collect();
                for (id, value) in outputs {
                    assert!(values.insert(id, value).is_none());
                }
            }
            RawOp::PackUnit { .. } | RawOp::LiftBasis { .. } | RawOp::Gate { .. } => {}
            other => panic!("unexpected operation outside this probe: {other:?}"),
        }
    }
}

fn assert_enum(value: &Value, name: &str, labels: &[&str], width: usize) {
    let Value::Enumeration(ty, ids) = value else {
        panic!("lost typed enum");
    };
    let Kind::Nominal(nominal) = &ty.kind else {
        panic!("lost original type");
    };
    assert_eq!(nominal.origin.module, "main");
    assert_eq!(nominal.origin.name, name);
    let Body::Enum(actual) = &nominal.body else {
        panic!("changed declaration kind");
    };
    assert_eq!(actual, labels);
    assert_eq!(ids.len(), width);
    assert_eq!(
        ty.basis_bits(),
        None,
        "enum is not an unrestricted bit word"
    );
}

#[test]
fn measured_tri_proposal_retains_both_histories_and_simultaneous_tag_phis() {
    let project = project(FIRST);
    let (value, raw, effect) = raw_main(&project);
    let Value::Classical(output) = value else {
        panic!("Bit result");
    };
    assert_eq!(effect, Effect::Observe);
    assert!(
        raw.registers.is_empty(),
        "measurement consumes the complete owner"
    );
    let [
        RawOp::PackUnit { output: unit },
        RawOp::LiftBasis {
            input,
            output: prepared,
            output_wires,
            table,
        },
        RawOp::Gate {
            gate,
            input: gate_input,
            output: evolved,
        },
        RawOp::MeasureZ {
            input: measured, ..
        },
        ..,
    ] = raw.operations.as_slice()
    else {
        panic!("exact preparation/phase/observation prefix changed");
    };
    assert_eq!(unit, input);
    assert_eq!(prepared, gate_input);
    assert_eq!(evolved, measured);
    assert_eq!(output_wires.len(), 1);
    assert_eq!(table, &[0]);
    assert_eq!(*gate, SingleGate::H);
    let RawOp::ClassicalBranch {
        then_ops,
        else_ops,
        classical_phis,
        quantum_phis,
        ..
    } = &raw.operations[4]
    else {
        panic!("choose is an actual conditional");
    };
    assert!(quantum_phis.is_empty());
    assert_eq!(classical_phis.len(), 2);
    for (ops, expected) in [(then_ops, [true, false]), (else_ops, [false, true])] {
        assert_eq!(ops.len(), 2);
        for (op, value) in ops.iter().zip(expected) {
            assert!(matches!(op, RawOp::ClassicalConst { value: actual, .. } if *actual == value));
        }
    }
    for outcome in [false, true] {
        let mut values = BTreeMap::new();
        classical_history(&raw.operations, outcome, &mut values);
        assert_eq!(values[&output], outcome);
    }
}

#[test]
fn all_three_constructors_keep_original_identity_and_order() {
    for (variant, ordinal) in [("A", 0usize), ("B", 1), ("C", 2)] {
        let text = format!("enum Tri {{ A, B, C }} fn main() -> Tri {{ Tri::{variant} }}");
        let (value, raw, effect) = raw_main(&project(&text));
        assert_enum(&value, "Tri", &["A", "B", "C"], 2);
        let Value::Enumeration(ty, ids) = value else {
            unreachable!()
        };
        let Kind::Nominal(nominal) = &ty.kind else {
            unreachable!()
        };
        assert_eq!(&*nominal.origin.source, text);
        assert_eq!(effect, Effect::Unitary);
        let mut values = BTreeMap::new();
        classical_history(&raw.operations, false, &mut values);
        assert_eq!(
            ids.iter().enumerate().fold(0usize, |tag, (axis, id)| tag
                | ((values[id] as usize) << axis)),
            ordinal
        );
    }
}

#[test]
fn singleton_branch_retains_zero_width_nominal_node() {
    let text = "use std::state::init0; enum One { Only } fn choose(b: Bit) -> One { if b { One::Only } else { One::Only } } observe fn main() -> One { choose(measure_z(h(init0()))) }";
    let (value, raw, effect) = raw_main(&project(text));
    assert_enum(&value, "One", &["Only"], 0);
    assert_ne!(value.ty(), Ty::unit());
    assert_ne!(value.ty(), Ty::empty_bits());
    assert_eq!(effect, Effect::Observe);
    assert!(raw.registers.is_empty());
    let RawOp::ClassicalBranch {
        classical_phis,
        quantum_phis,
        ..
    } = raw.operations.last().unwrap()
    else {
        panic!("singleton still joins the conditional");
    };
    assert!(classical_phis.is_empty());
    assert!(quantum_phis.is_empty());
}

#[test]
fn enum_join_preserves_the_complete_zero_width_quantum_frame() {
    let text = "enum Tri { A, B, C } unitary fn keep(b: Bit, q: Q<Unit>) -> (Tri, Q<Unit>) { if b { (Tri::B, q) } else { (Tri::C, q) } }";
    let project = project(text);
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::keep").unwrap();
    let mut lower = lowerer(&mut compiler);
    let condition = lower.classical();
    let returned = lower.register(Ty::unit(), Vec::new());
    let suspended = lower.raw.register(Ty::empty_bits(), Vec::new());
    let old_suspended = lower.raw.registers[&suspended].token;
    let value = lower
        .call_user(&key, vec![Value::Classical(condition), returned], None)
        .unwrap();
    let fields = value.into_fields().unwrap();
    assert_enum(&fields[0], "Tri", &["A", "B", "C"], 2);
    assert_eq!(fields[1].ty(), Ty::quantum(Ty::unit()));
    assert_eq!(lower.raw.registers.len(), 2);
    assert_eq!(lower.raw.registers[&suspended].basis, Ty::empty_bits());
    assert_ne!(lower.raw.registers[&suspended].token, old_suspended);
    let RawOp::ClassicalBranch {
        quantum_phis,
        classical_phis,
        ..
    } = lower.raw.operations.last().unwrap()
    else {
        panic!("actual branch");
    };
    assert_eq!(
        quantum_phis.len(),
        2,
        "returned and suspended zero-width owners"
    );
    assert!(quantum_phis.iter().all(|phi| phi.output_wires.is_empty()));
    assert_eq!(classical_phis.len(), 2);
}

#[test]
fn finite_table_refuses_nominal_domain_before_enumerating_spare_tag() {
    let project = project(FIRST);
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::is_b").unwrap();
    let error = compiler
        .compile_basis(&key)
        .err()
        .expect("no unrestricted four-row table for Tri");
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(error.message.contains("finite table"));
    assert!(compiler.basis.is_empty());
}

#[test]
fn production_gate_still_refuses_reachable_intermediate_and_dormant_nominals() {
    for text in [
        FIRST,
        "enum Tri { A, B, C } fn dormant() -> Tri { Tri::A } fn main() -> Bit { 0 }",
    ] {
        let project = project(text);
        let error = prepare_original_source(Path::new("main.qli"), &project)
            .err()
            .expect("global production gate");
        assert_eq!(error.code, ErrorCode::Unsupported);
        assert!(error.message.contains("typed native transport"));
    }
    let mut imported = project("fn main() -> Bit { 0 }");
    imported.modules.insert(
        "hidden".into(),
        source_module("hidden", "enum Hidden { A, B, C }", ModuleOrigin::Local),
    );
    let error = prepare_original_source(Path::new("main.qli"), &imported)
        .err()
        .expect("all retained modules are gated");
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(error.message.contains("typed native transport"));
}

#[test]
fn all_match_arms_pass_common_types_and_effects_before_proposal() {
    for text in [
        "enum Tri { A, B, C } classical fn is_b(t: Tri) -> Bit { match t { Tri::A => 0, Tri::B => 1, Tri::B => 0 } }",
        "enum Tri { A, B, C } enum Other { A, B, C } classical fn is_b(t: Tri) -> Bit { match t { Tri::A => 0, Other::B => 1, Tri::C => 0 } }",
        "enum Tri { A, B, C } classical fn is_b(t: Tri) -> Bit { match t { Tri::A => 0, Tri::B => 1, Tri::C => () } }",
        "use std::state::init0; enum Tri { A, B, C } unitary fn hidden(t: Tri) -> Bit { match t { Tri::A => 0, Tri::B => 1, Tri::C => measure_z(init0()) } }",
    ] {
        let project = project(text);
        assert!(
            prepare_untrusted_source_test(Path::new("main.qli"), &project).is_err(),
            "must reject every original arm: {text}"
        );
    }
}

#[test]
fn copying_the_same_enum_reuses_ids_without_phi_destinations() {
    let text = "enum Tri { A, B, C } fn main() -> Tri { let t = Tri::B; if 1 { t } else { t } }";
    let (value, raw, _) = raw_main(&project(text));
    assert_enum(&value, "Tri", &["A", "B", "C"], 2);
    let RawOp::ClassicalBranch { classical_phis, .. } = raw.operations.last().unwrap() else {
        panic!("actual branch");
    };
    assert!(classical_phis.is_empty());
    let Value::Enumeration(_, ids) = value else {
        unreachable!()
    };
    let mut values = BTreeMap::new();
    classical_history(&raw.operations, false, &mut values);
    assert!(values[&ids[0]]);
    assert!(!values[&ids[1]]);
}

#[test]
fn match_expansion_obeys_the_existing_recursion_limit() {
    // Stay within the source member limit so this reaches lowering. The
    // surrounding function/expression frames also consume the depth budget.
    // This classical syntax case creates no quantum dimensions.
    let labels: Vec<_> = (0..64).map(|i| format!("V{i}")).collect();
    let arms = labels
        .iter()
        .map(|name| format!("Many::{name} => 0"))
        .collect::<Vec<_>>()
        .join(", ");
    let text = format!(
        "enum Many {{ {} }} classical fn pick(t: Many) -> Bit {{ match t {{ {arms} }} }} fn main() -> Bit {{ pick(Many::V0) }}",
        labels.join(", ")
    );
    let project = project(&text);
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::main").unwrap();
    let mut lower = lowerer(&mut compiler);
    let error = lower
        .call_user(&key, Vec::new(), None)
        .expect_err("bounded branch expansion");
    assert_eq!(error.code, ErrorCode::Limit);
    assert!(error.message.contains("depth limit"));
    assert_eq!(
        lower.depth, 0,
        "refused expansion restores its caller depth"
    );
}

#[test]
fn permuted_match_labels_select_each_original_ordinal() {
    let text = "enum Tri { A, B, C } classical fn is_b(t: Tri) -> Bit { match t { Tri::C => 0, Tri::A => 0, Tri::B => 1 } } fn main() -> (Bit, Bit, Bit) { (is_b(Tri::A), is_b(Tri::B), is_b(Tri::C)) }";
    let (value, raw, effect) = raw_main(&project(text));
    assert_eq!(effect, Effect::Unitary);
    let mut values = BTreeMap::new();
    classical_history(&raw.operations, false, &mut values);
    let fields = value.into_fields().unwrap();
    let actual: Vec<_> = fields
        .iter()
        .map(|value| match value {
            Value::Classical(id) => values[id],
            _ => panic!("ordinary Bit field"),
        })
        .collect();
    assert_eq!(actual, [false, true, false]);
}

#[test]
fn original_bytes_and_private_type_visibility_precede_raw_generation() {
    let mut changed = project("enum Tri { A, B, C } fn main() -> Tri { Tri::A }");
    let crate::frontend::ast::TypeDeclKind::Enum { variants } =
        &mut changed.modules.get_mut("main").unwrap().ast.type_decls[0].kind
    else {
        unreachable!()
    };
    variants.swap(0, 1);
    let error = prepare_untrusted_source_test(Path::new("main.qli"), &changed)
        .err()
        .expect("mutated AST");
    assert!(error.message.contains("original bytes"));

    let mut private = project("use hidden::Tri; fn main() -> Tri { Tri::A }");
    private.modules.insert(
        "hidden".into(),
        source_module("hidden", "enum Tri { A, B, C }", ModuleOrigin::Local),
    );
    assert!(prepare_untrusted_source_test(Path::new("main.qli"), &private).is_err());
}
