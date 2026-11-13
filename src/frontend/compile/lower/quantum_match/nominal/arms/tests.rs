//! Producer-only direct primitive subjects; no native executable is selected.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::compile::lower::call_state_tests::untrusted_compiler;
use crate::frontend::project::{ModuleOrigin, ProjectEdition, SourceModule};
use crate::interchange::carrier::Atom;
use crate::interchange::qmatch::{OperationNode, OperationPrimitive};

const H_NOMINAL: &str = r#"#![no_implicit_prelude]
pub enum Tag { A, B }
pub unitary fn main(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {
    qmatch(s, q) { Tag::A => h, Tag::B => h }
}
"#;
const GLOBAL_UNIT: &str = r#"#![no_implicit_prelude]
pub enum Tag { A, B }
pub unitary fn main(s: Q<Tag>, u: Q<Unit>) -> (Q<Tag>, Q<Unit>) {
    qmatch(s, u) { Tag::A => global_phase_eighth, Tag::B => global_phase_eighth }
}
"#;

fn retained_primitive(source: &str, kind: OperationPrimitive, target_atoms: &[Atom]) {
    let project = Project {
        edition_context: ProjectEdition::Explicit(crate::edition::Edition::E2026),
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: source.into(),
                ast: crate::frontend::parser::parse_module(source).expect("original first source"),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    };
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::main").unwrap();
    let (parameters, _) = compiler.signature(&key).unwrap();
    let Kind::Q(target) = &parameters[1].kind else {
        panic!("exact quantum target")
    };
    let bits = target.basis_width().unwrap() as usize;
    let declaration = project.modules["main"]
        .ast
        .decls
        .iter()
        .find(|declaration| declaration.name.text == "main")
        .unwrap();
    let FnBody::Quantum(block) = &declaration.body else {
        panic!("original runtime body")
    };
    let ExprKind::QuantumMatch(selection) = &block.result.kind else {
        panic!("original qmatch")
    };
    let mut lower = Lowerer {
        compiler: &mut compiler,
        raw: RawState::new(),
        operation_sources: BTreeMap::new(),
        instrument_calls: Vec::new(),
        nominal_modules: std::rc::Rc::new(std::cell::RefCell::new(BTreeSet::new())),
        nominal_basis_used: None,
        nominal_qmatch: None,
        source_context: None,
        tuple_binding_origins: vec![BTreeMap::new()],
        access_updates: vec![BTreeSet::new()],
        effect: Effect::Unitary,
        contract_effect: Effect::Unitary,
        effect_source: None,
        depth: 0,
        bindings: BTreeMap::new(),
    };
    for arm in &selection.arms {
        let (body, steps, operation) = prepare(
            &mut lower,
            "main",
            &arm.operation,
            target,
            bits,
            &Env::new(),
        )
        .expect("untrusted direct primitive preparation");
        let ArmBody::Program(raw) = body else {
            panic!("primitive became a function provider")
        };
        assert_eq!(raw.quantum_inputs.len(), 1);
        assert_eq!(raw.quantum_inputs[0].wires.len(), bits);
        assert_eq!(raw.quantum_outputs, [TokenId(1)]);
        assert!(raw.classical_inputs.is_empty() && raw.classical_outputs.is_empty());
        assert_eq!(operation.description.root, 0);
        assert_eq!(
            operation.description.nodes,
            [OperationNode::Primitive {
                kind,
                target: target_atoms.to_vec(),
            }]
        );
        assert!(operation.bodies.is_empty());

        assert_eq!(steps.len(), 1);
        assert_eq!(
            steps[0].controls,
            [BitControl {
                index: 0,
                when_one: true
            }]
        );
        match kind {
            OperationPrimitive::H => {
                assert!(matches!(
                    &raw.operations[..],
                    [RawOp::Gate {
                        gate: SingleGate::H,
                        ..
                    }]
                ));
                assert!(matches!(
                    &steps[0].action,
                    CircuitAction::Hadamard { target: 1 }
                ));
            }
            OperationPrimitive::GlobalPhaseEighth => {
                assert!(raw.quantum_inputs[0].wires.is_empty());
                assert!(
                    matches!(&raw.operations[..], [RawOp::ApplyUnitary { steps, .. }]
                    if matches!(&steps[..], [CircuitStep { action: CircuitAction::Monomial {
                        indices, permutation, phases }, .. }]
                        if indices.is_empty() && permutation == &[0] && phases == &[1]))
                );
                assert!(
                    matches!(&steps[0].action, CircuitAction::Monomial { indices, permutation, phases }
                    if indices.is_empty() && permutation == &[0] && phases == &[1])
                );
            }
        }
    }
    assert!(lower.compiler.checked.is_empty());
    assert!(lower.compiler.function_evidence.is_empty());
    assert!(lower.raw.operations.is_empty());
}

#[test]
fn direct_primitive_arms_keep_zero_provider_contexts_and_exact_unit_phase() {
    retained_primitive(H_NOMINAL, OperationPrimitive::H, &[Atom::Bit]);
    retained_primitive(
        GLOBAL_UNIT,
        OperationPrimitive::GlobalPhaseEighth,
        &[Atom::Unit],
    );
}
