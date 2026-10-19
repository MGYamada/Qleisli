//! Tiny descriptor controls; native receipts keep their own original meanings.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

fn identity_raw() -> RawProgram {
    RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![],
            shape: BasisShape { bits: 0 },
        }],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn evidence() -> Arc<FunctionEvidence> {
    let raw = identity_raw();
    Arc::new(
        FunctionEvidence::check(
            crate::edition::Edition::E2026,
            BasisType::Unit,
            raw.clone(),
            raw,
            crate::contract::function::FunctionIdentity {
                implementation: "main::identity".into(),
                specification: "main::identity".into(),
                sources: vec![(
                    "main".into(),
                    "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}".into(),
                )],
            },
            &mut Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap(),
    )
}

fn provider(evidence: Arc<FunctionEvidence>) -> Operation {
    Operation {
        basis: Ty::unit(),
        codomain: Ty::unit(),
        access: [true; 3],
        meaning: Some(evidence.meaning().clone()),
        effect: Effect::Unitary,
        node: Arc::new(Node::Provider(evidence)),
        depth: 1,
        nodes: 1,
    }
}

fn repeat(count: u16, child: Operation) -> Operation {
    Operation {
        depth: child.depth + 1,
        nodes: child.nodes + 1,
        node: Arc::new(Node::Repeat(count, child.clone())),
        ..child
    }
}

fn then(left: Operation, right: Operation) -> Operation {
    Operation {
        depth: 1 + left.depth.max(right.depth),
        nodes: 1 + left.nodes + right.nodes,
        node: Arc::new(Node::Then(left.clone(), right)),
        ..left
    }
}

fn same(left: &Operation, right: &Operation) -> bool {
    left.same_descriptor_budgeted(right, &mut |_| Ok::<_, ()>(()))
        .unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn issued_provider_identity_and_order_survive_equal_matrices() {
    let first = provider(evidence());
    let second = provider(evidence());
    assert_eq!(first.meaning, second.meaning);
    assert!(same(&first, &first.clone()));
    assert!(!same(&first, &second));
    assert!(!same(
        &then(first.clone(), second.clone()),
        &then(second, first),
    ));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn zero_power_retains_child_receipt_count_and_constructor() {
    let first = provider(evidence());
    let second = provider(evidence());
    assert!(!same(&repeat(0, first.clone()), &repeat(0, second)));
    assert!(!same(&repeat(0, first.clone()), &repeat(1, first.clone())));
    assert!(!same(
        &repeat(0, first.clone()),
        &repeat(0, repeat(0, first.clone())),
    ));
    let mut inverse = repeat(0, first.clone());
    inverse.node = Arc::new(Node::Inverse(first.clone()));
    assert!(!same(&repeat(0, first), &inverse));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn shared_node_still_compares_both_ports_phase_effect_and_access() {
    let original = provider(evidence());
    // Only private descriptor metadata is varied. These mutations neither
    // change the issued receipt nor claim acceptance of a different body.
    let mut variants = Vec::new();
    let mut changed = original.clone();
    changed.basis = Ty::empty_bits();
    variants.push(changed);
    let mut changed = original.clone();
    changed.codomain = Ty::empty_bits();
    variants.push(changed);
    let mut changed = original.clone();
    changed.meaning = Some(Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap());
    variants.push(changed);
    let mut changed = original.clone();
    changed.effect = Effect::Observe;
    variants.push(changed);
    for index in 0..3 {
        let mut changed = original.clone();
        changed.access[index] = false;
        variants.push(changed);
    }
    for changed in variants {
        assert!(Arc::ptr_eq(&original.node, &changed.node));
        assert!(!same(&original, &changed));
    }
    let mut low = original.clone();
    low.basis = Ty::pair(Ty::unit(), Ty::bit());
    let mut high = original;
    high.basis = Ty::pair(Ty::bit(), Ty::unit());
    assert_eq!(low.basis.basis_bits(), high.basis.basis_bits());
    assert!(!same(&low, &high));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn explicit_meaning_reference_survives_equal_matrices_and_shared_child() {
    use crate::frontend::project::{ModuleOrigin, SourceModule};
    let text = "classical fn identity(u:Unit)->Unit{u}\nmeaning First:Unit=permutation_by(identity);\nmeaning Second:Unit=permutation_by(identity);";
    let project = Project {
        edition_context: crate::frontend::project::ProjectEdition::Explicit(
            crate::edition::Edition::E2026,
        ),
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: text.into(),
                ast: crate::frontend::parser::parse_module(text).unwrap(),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    };
    let compiler = super::super::snapshot_tests::compiler(&project);
    let first = compiler.source.resolution.qualified("main::First").unwrap();
    let second = compiler
        .source
        .resolution
        .qualified("main::Second")
        .unwrap();
    let child = provider(evidence());
    let requested = |meaning| Operation {
        node: Arc::new(Node::Requested(meaning, child.clone())),
        depth: child.depth + 1,
        nodes: child.nodes + 1,
        ..child.clone()
    };
    assert!(same(&requested(first), &requested(first)));
    assert_eq!(requested(first).meaning, requested(second).meaning);
    assert!(!same(&requested(first), &requested(second)));
    assert!(!same(&requested(first), &child));
    assert!(!same(
        &repeat(0, requested(first)),
        &repeat(0, requested(second))
    ));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn pure_descriptor_keeps_its_optional_inverse_issued_identity() {
    let kernel =
        crate::interchange::native::Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let leaf = Arc::new(
        crate::frontend::pure::check(
            &kernel,
            &identity_raw(),
            &BasisType::Unit,
            &BasisType::Unit,
            None,
            &mut Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap(),
    );
    let first = evidence();
    let second = evidence();
    let make = |inverse| Operation {
        node: Arc::new(Node::Pure(PureProvider {
            origin: None,
            leaf: Arc::clone(&leaf),
            inverse,
        })),
        ..provider(Arc::clone(&first))
    };
    // The production constructor fixes one inverse per fresh leaf. These are
    // robustness controls for complete identity, not a reachable capability bug.
    assert!(same(
        &make(Some(Arc::clone(&first))),
        &make(Some(Arc::clone(&first))),
    ));
    assert!(!same(&make(Some(second)), &make(None)));
    assert!(!same(&make(Some(evidence())), &make(Some(evidence()))));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn exhausted_matching_child_comparison_refuses_instead_of_returning_false() {
    let leaf = provider(evidence());
    let left = repeat(0, repeat(0, leaf.clone()));
    let right = repeat(0, repeat(0, leaf));
    let mut complete_cost = 0;
    assert!(
        left.same_descriptor_budgeted(&right, &mut |cells| {
            complete_cost += cells;
            Ok::<_, ()>(())
        })
        .unwrap()
    );
    for capacity in [0, complete_cost - 1] {
        let mut remaining = capacity;
        assert_eq!(
            left.same_descriptor_budgeted(&right, &mut |cells| {
                if cells > remaining {
                    Err("work limit")
                } else {
                    remaining -= cells;
                    Ok(())
                }
            }),
            Err("work limit"),
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn registry_hit_charges_work_and_failure_does_not_register_a_miss() {
    use crate::frontend::project::{ModuleOrigin, SourceModule};
    let text = "unitary fn hold[const U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Applicable(U){U(q)}";
    let project = Project {
        edition_context: crate::frontend::project::ProjectEdition::Explicit(
            crate::edition::Edition::E2026,
        ),
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: text.into(),
                ast: crate::frontend::parser::parse_module(text).unwrap(),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    };
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler.source.resolution.declarations().next().unwrap().0;
    let value = provider(evidence());
    compiler
        .record_operation_instance(key, vec![value.clone()], "main", Span::default())
        .unwrap();
    let before = compiler.work;
    compiler
        .record_operation_instance(key, vec![value.clone()], "main", Span::default())
        .unwrap();
    assert_eq!(compiler.instances.len(), 1);
    assert!(compiler.work > before);
    compiler.work = MAX_WORK - 1;
    let error = compiler
        .record_operation_instance(key, vec![value], "main", Span::default())
        .unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit);
    assert_eq!(compiler.instances.len(), 1);
    assert_eq!(compiler.work, MAX_WORK);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn pure_descriptor_keeps_original_source_origin_even_with_the_same_native_leaf() {
    use crate::frontend::project::{ModuleOrigin, SourceModule};
    let text = "unitary fn first(q:Q<Unit>)->Q<Unit>{q}\nunitary fn second(q:Q<Unit>)->Q<Unit>{q}";
    let project = Project {
        edition_context: crate::frontend::project::ProjectEdition::Explicit(
            crate::edition::Edition::E2026,
        ),
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: text.into(),
                ast: crate::frontend::parser::parse_module(text).unwrap(),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    };
    let compiler = super::super::snapshot_tests::compiler(&project);
    let foreign = super::super::snapshot_tests::compiler(&project);
    let first = compiler.source.resolution.qualified("main::first").unwrap();
    let second = compiler
        .source
        .resolution
        .qualified("main::second")
        .unwrap();
    let kernel =
        crate::interchange::native::Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let leaf = Arc::new(
        crate::frontend::pure::check(
            &kernel,
            &identity_raw(),
            &BasisType::Unit,
            &BasisType::Unit,
            None,
            &mut Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap(),
    );
    let rows = Arc::new(vec![Arc::new(("main".into(), text.into()))]);
    let origin = |key, table| {
        let path = compiler.source.resolution.path(key);
        let equation = Arc::new(
            crate::interchange::pure_leaf::SourcePureEquation::bind(
                Arc::clone(&leaf),
                Arc::clone(&leaf),
                (path.clone(), path),
                Arc::clone(&rows),
            )
            .unwrap(),
        );
        Arc::new(PureOrigin {
            definition: key,
            table,
            meaning: None,
            equation,
        })
    };
    let first_origin = origin(first, Arc::clone(&compiler.source.lexical[&first]));
    let second_origin = origin(second, Arc::clone(&compiler.source.lexical[&second]));
    let foreign_origin = origin(first, Arc::clone(&foreign.source.lexical[&first]));
    let inverse = evidence();
    let make = |origin| Operation {
        node: Arc::new(Node::Pure(PureProvider {
            origin,
            leaf: Arc::clone(&leaf),
            inverse: Some(Arc::clone(&inverse)),
        })),
        ..provider(Arc::clone(&inverse))
    };
    let original = make(Some(Arc::clone(&first_origin)));
    assert!(same(&original, &make(Some(first_origin))));
    for other in [
        make(Some(second_origin)),
        make(Some(foreign_origin)),
        make(None),
    ] {
        assert_eq!(original.meaning, other.meaning);
        assert!(!same(&original, &other));
        assert!(!same(&repeat(0, original.clone()), &repeat(0, other)));
    }
}
