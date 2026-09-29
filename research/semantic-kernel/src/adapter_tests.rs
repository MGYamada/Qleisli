use super::*;
use crate::kernel::Contract;
use qleisli::ir::{BasisShape, BitControl, QuantumPort};

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
    }
}

fn raw(inputs: Vec<QuantumPort>, operations: Vec<RawOp>, outputs: &[u32]) -> RawProgram {
    RawProgram {
        quantum_inputs: inputs,
        classical_inputs: vec![],
        operations,
        quantum_outputs: outputs.iter().copied().map(TokenId).collect(),
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    }
}

fn gate(gate: SingleGate, input: u32, output: u32) -> RawOp {
    RawOp::Gate {
        gate,
        input: TokenId(input),
        output: TokenId(output),
    }
}

fn add(graph: &mut TermGraph, term: Term) -> TermId {
    let id = TermId(graph.terms.len());
    graph.terms.push(term);
    id
}

fn leaf(
    imported: &ImportedProgram,
    graph: &TermGraph,
    contract: Contract,
) -> Result<BoundProgram, AdapterError> {
    imported.check(
        graph,
        &[ProofRule::ExactLeaf { contract }],
        ProofId(0),
        &RequiredContract::new(graph.clone(), contract),
        Limits::default(),
    )
}

#[test]
fn raw_hadamards_satisfy_a_separately_required_identity() {
    let program = raw(
        vec![port(0, &[73])],
        vec![gate(SingleGate::H, 0, 1), gate(SingleGate::H, 1, 2)],
        &[2],
    );
    let imported = import_raw(program.clone()).unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: identity,
    };
    let bound = leaf(&imported, &graph, contract).unwrap();
    bound.check_binding(&program).unwrap();
    let changed = raw(
        vec![port(0, &[73])],
        vec![gate(SingleGate::H, 0, 1), gate(SingleGate::X, 1, 2)],
        &[2],
    );
    assert!(matches!(
        bound.check_binding(&changed),
        Err(AdapterError::Binding(_))
    ));
}

#[test]
fn graph_edits_and_a_different_implementation_root_are_rejected() {
    let imported = import_raw(raw(
        vec![port(0, &[0])],
        vec![gate(SingleGate::Z, 0, 1)],
        &[1],
    ))
    .unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let z = add(&mut graph, Term::Z);
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: z,
    };
    let mut wrong_contract = contract;
    wrong_contract.implementation = z;
    assert!(matches!(
        leaf(&imported, &graph, wrong_contract),
        Err(AdapterError::Binding(_))
    ));
    graph.terms[0] = Term::X;
    assert!(matches!(
        leaf(&imported, &graph, contract),
        Err(AdapterError::Binding(_))
    ));
}

#[test]
fn physical_auxiliary_implementations_share_an_encoded_z_contract() {
    let direct = raw(
        vec![port(0, &[20]), port(1, &[90])],
        vec![gate(SingleGate::Z, 0, 2)],
        &[2, 1],
    );
    let auxiliary = raw(
        vec![port(0, &[20]), port(1, &[90])],
        vec![
            RawOp::Cnot {
                control: TokenId(0),
                target: TokenId(1),
                control_out: TokenId(2),
                target_out: TokenId(3),
            },
            gate(SingleGate::Z, 3, 4),
            RawOp::Cnot {
                control: TokenId(2),
                target: TokenId(4),
                control_out: TokenId(5),
                target_out: TokenId(6),
            },
        ],
        &[5, 6],
    );
    for program in [direct, auxiliary] {
        let imported = import_raw(program).unwrap();
        let mut graph = imported.graph().clone();
        let encoding = add(
            &mut graph,
            Term::ZeroExtend {
                logical: TypeId(1),
                scratch: TypeId(1),
            },
        );
        let z = add(&mut graph, Term::Z);
        let contract = Contract {
            implementation: imported.implementation(),
            input_encoding: encoding,
            output_encoding: encoding,
            logical: z,
        };
        let bound = leaf(&imported, &graph, contract).unwrap();
        // The theorem has physical input/output ownership for both wires. It
        // neither initializes the auxiliary nor exposes a release operation.
        assert_eq!(bound.raw().quantum_inputs.len(), 2);
        assert_eq!(bound.raw().quantum_outputs.len(), 2);
    }
}

#[test]
fn auxiliary_x_does_not_satisfy_zero_return() {
    let imported = import_raw(raw(
        vec![port(0, &[0]), port(1, &[1])],
        vec![gate(SingleGate::X, 1, 2)],
        &[0, 2],
    ))
    .unwrap();
    let mut graph = imported.graph().clone();
    let encoding = add(
        &mut graph,
        Term::ZeroExtend {
            logical: TypeId(1),
            scratch: TypeId(1),
        },
    );
    let identity = add(&mut graph, Term::Identity { space: TypeId(1) });
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: encoding,
        output_encoding: encoding,
        logical: identity,
    };
    assert!(matches!(
        leaf(&imported, &graph, contract),
        Err(AdapterError::Kernel(_))
    ));
}

#[test]
fn output_order_is_a_semantic_transport_and_a_binding_dependency() {
    let program = raw(vec![port(0, &[9]), port(1, &[3])], vec![], &[1, 0]);
    let imported = import_raw(program.clone()).unwrap();
    assert_eq!(imported.output_wires(), &[WireId(3), WireId(9)]);
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let swap = add(
        &mut graph,
        Term::Rewire {
            input: imported.space(),
            output: imported.space(),
            output_axes: vec![1, 0],
        },
    );
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: swap,
    };
    let bound = leaf(&imported, &graph, contract).unwrap();
    let mut reordered = program;
    reordered.quantum_outputs.reverse();
    assert!(bound.check_binding(&reordered).is_err());
    let mut wrong = contract;
    wrong.logical = identity;
    assert!(leaf(&imported, &graph, wrong).is_err());
}

#[test]
fn split_join_and_nonadjacent_gate_axes_preserve_wire_order() {
    let program = raw(
        vec![port(0, &[7, 4])],
        vec![
            RawOp::Split {
                input: TokenId(0),
                left: TokenId(1),
                right: TokenId(2),
                left_bits: 1,
            },
            gate(SingleGate::Z, 2, 3),
            RawOp::Join {
                left: TokenId(3),
                right: TokenId(1),
                output: TokenId(4),
            },
        ],
        &[4],
    );
    let imported = import_raw(program).unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let bit_identity = add(&mut graph, Term::Identity { space: TypeId(1) });
    let z = add(&mut graph, Term::Z);
    let on_high = add(
        &mut graph,
        Term::Tensor {
            low: bit_identity,
            high: z,
        },
    );
    let swap = add(
        &mut graph,
        Term::Rewire {
            input: imported.space(),
            output: imported.space(),
            output_axes: vec![1, 0],
        },
    );
    let meaning = add(
        &mut graph,
        Term::Sequence {
            first: on_high,
            second: swap,
        },
    );
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: meaning,
    };
    leaf(&imported, &graph, contract).unwrap();
}

#[test]
fn scalar_phase_on_zero_wires_is_retained() {
    let program = raw(
        vec![port(0, &[])],
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![],
                    permutation: vec![0],
                    phases: vec![4],
                },
            }],
        }],
        &[1],
    );
    let imported = import_raw(program).unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let phase = add(
        &mut graph,
        Term::Phase {
            space: imported.space(),
            eighths: 4,
        },
    );
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: phase,
    };
    leaf(&imported, &graph, contract).unwrap();
    let mut wrong = contract;
    wrong.logical = identity;
    assert!(leaf(&imported, &graph, wrong).is_err());
}

#[test]
fn a_zero_controlled_scalar_phase_is_not_erased() {
    let imported = import_raw(raw(
        vec![port(0, &[11])],
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![CircuitStep {
                controls: vec![BitControl {
                    index: 0,
                    when_one: false,
                }],
                action: CircuitAction::Monomial {
                    indices: vec![],
                    permutation: vec![0],
                    phases: vec![4],
                },
            }],
        }],
        &[1],
    ))
    .unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let phase = add(
        &mut graph,
        Term::Phase {
            space: imported.space(),
            eighths: 4,
        },
    );
    let z = add(&mut graph, Term::Z);
    let negative_z = add(
        &mut graph,
        Term::Sequence {
            first: phase,
            second: z,
        },
    );
    let contract = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: negative_z,
    };
    leaf(&imported, &graph, contract).unwrap();
    let mut wrong = contract;
    wrong.logical = z;
    assert!(leaf(&imported, &graph, wrong).is_err());
}

#[test]
fn ordinary_ownership_checks_reject_aliasing_and_missing_unit_owner() {
    let aliased = raw(
        vec![port(0, &[5])],
        vec![RawOp::Cnot {
            control: TokenId(0),
            target: TokenId(0),
            control_out: TokenId(1),
            target_out: TokenId(2),
        }],
        &[1, 2],
    );
    assert!(matches!(
        import_raw(aliased),
        Err(AdapterError::InvalidIr(_))
    ));
    assert!(matches!(
        import_raw(raw(vec![port(0, &[])], vec![], &[])),
        Err(AdapterError::InvalidIr(_))
    ));
}

#[test]
fn unsupported_valid_pure_raw_operations_are_rejected_explicitly() {
    let basis_lift = raw(
        vec![port(0, &[4])],
        vec![RawOp::LiftBasis {
            input: TokenId(0),
            output: TokenId(1),
            output_wires: vec![WireId(4)],
            table: vec![1, 0],
        }],
        &[1],
    );
    qleisli::verify(basis_lift.clone()).unwrap();
    assert!(matches!(
        import_raw(basis_lift),
        Err(AdapterError::Unsupported(_))
    ));
}

#[test]
fn large_multiport_identity_binds_without_dense_leaf_checking() {
    let inputs: Vec<_> = (0..128).map(|id| port(id, &[id + 300])).collect();
    let outputs: Vec<_> = (0..128).collect();
    let program = raw(inputs, vec![], &outputs);
    let imported = import_raw(program).unwrap();
    let graph = imported.graph();
    let identity = imported.implementation();
    let expected = Contract {
        implementation: identity,
        input_encoding: identity,
        output_encoding: identity,
        logical: identity,
    };
    imported
        .check(
            graph,
            &[ProofRule::Identity { encoding: identity }],
            ProofId(0),
            &RequiredContract::new(graph.clone(), expected),
            Limits::default(),
        )
        .unwrap();
}

#[test]
fn a_local_z_binds_to_actual_128_bit_raw_ir_with_only_a_one_bit_leaf() {
    let inputs: Vec<_> = (0..128).map(|id| port(id, &[id + 1000])).collect();
    let mut outputs: Vec<_> = (0..128).collect();
    outputs[0] = 200;
    let imported = import_raw(raw(inputs, vec![gate(SingleGate::Z, 0, 200)], &outputs)).unwrap();
    let mut graph = imported.graph().clone();
    // Independently require Z on the low bit and identity on the 127-bit
    // frame. The raw importer chooses exactly this physical tensor structure.
    let bit_id = add(&mut graph, Term::Identity { space: TypeId(1) });
    let frame_id = add(&mut graph, Term::Identity { space: TypeId(127) });
    let z = add(&mut graph, Term::Z);
    let encoding = add(
        &mut graph,
        Term::Tensor {
            low: bit_id,
            high: frame_id,
        },
    );
    let meaning = add(
        &mut graph,
        Term::Tensor {
            low: z,
            high: frame_id,
        },
    );
    let local = Contract {
        implementation: z,
        input_encoding: bit_id,
        output_encoding: bit_id,
        logical: z,
    };
    let expected = Contract {
        implementation: imported.implementation(),
        input_encoding: encoding,
        output_encoding: encoding,
        logical: meaning,
    };
    let proofs = vec![
        ProofRule::ExactLeaf { contract: local },
        ProofRule::Identity { encoding: frame_id },
        ProofRule::Tensor {
            low: ProofId(0),
            high: ProofId(1),
        },
    ];
    let bound = imported
        .check(
            &graph,
            &proofs,
            ProofId(2),
            &RequiredContract::new(graph.clone(), expected),
            Limits::default(),
        )
        .unwrap();
    assert_eq!(bound.evidence().stats().largest_matrix_dimension, 2);
    assert_eq!(bound.evidence().stats().exact_leaves, 1);
    assert_eq!(bound.raw().quantum_inputs.len(), 128);
}

#[test]
fn import_work_is_bounded_before_building_axis_transports() {
    let inputs: Vec<_> = (0..128).map(|id| port(id, &[id + 1000])).collect();
    let operations: Vec<_> = (0..400)
        .map(|id| gate(SingleGate::H, id + 1000, id + 1001))
        .collect();
    let oversized = raw(inputs, operations, &[]);
    assert!(matches!(import_raw(oversized), Err(AdapterError::Limit(_))));
}

#[test]
fn monomial_phase_is_applied_before_its_permutation() {
    let imported = import_raw(raw(
        vec![port(0, &[8])],
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![0],
                    permutation: vec![1, 0],
                    phases: vec![0, 1],
                },
            }],
        }],
        &[1],
    ))
    .unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let t = add(&mut graph, Term::T);
    let x = add(&mut graph, Term::X);
    let meaning = add(
        &mut graph,
        Term::Sequence {
            first: t,
            second: x,
        },
    );
    let reverse = add(
        &mut graph,
        Term::Sequence {
            first: x,
            second: t,
        },
    );
    let expected = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical: meaning,
    };
    leaf(&imported, &graph, expected).unwrap();
    assert!(
        leaf(
            &imported,
            &graph,
            Contract {
                logical: reverse,
                ..expected
            }
        )
        .is_err()
    );
}

#[test]
fn raw_toffoli_preserves_the_order_of_both_controls_and_the_target() {
    let imported = import_raw(raw(
        vec![port(0, &[12]), port(1, &[9]), port(2, &[7])],
        vec![RawOp::Toffoli {
            control_a: TokenId(0),
            control_b: TokenId(1),
            target: TokenId(2),
            control_a_out: TokenId(3),
            control_b_out: TokenId(4),
            target_out: TokenId(5),
        }],
        &[3, 4, 5],
    ))
    .unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let cnot = add(&mut graph, Term::Cnot);
    let meaning = add(&mut graph, Term::Controlled { operand: cnot });
    leaf(
        &imported,
        &graph,
        Contract {
            implementation: imported.implementation(),
            input_encoding: identity,
            output_encoding: identity,
            logical: meaning,
        },
    )
    .unwrap();
}

#[test]
fn malformed_tables_reject_before_importer_indexes_entries() {
    let program = raw(
        vec![port(0, &[])],
        vec![RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![],
                    permutation: vec![0],
                    phases: vec![],
                },
            }],
        }],
        &[1],
    );
    assert!(matches!(
        import_raw(program),
        Err(AdapterError::InvalidIr(_))
    ));
}

#[test]
fn another_import_cannot_redefine_a_frozen_clients_z_requirement_as_x() {
    let original = import_raw(raw(
        vec![port(0, &[1])],
        vec![gate(SingleGate::Z, 0, 1)],
        &[1],
    ))
    .unwrap();
    let mut required_graph = original.graph().clone();
    let identity = add(
        &mut required_graph,
        Term::Identity {
            space: original.space(),
        },
    );
    let logical = add(&mut required_graph, Term::Z);
    let expected = Contract {
        implementation: original.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical,
    };
    let required = RequiredContract::new(required_graph, expected);

    // The alternative import uses the same IDs and same wire/port shape. Its
    // own U = X and submitted u = X agree, but neither changes the client's Z.
    let changed = import_raw(raw(
        vec![port(0, &[1])],
        vec![gate(SingleGate::X, 0, 1)],
        &[1],
    ))
    .unwrap();
    let mut submitted = changed.graph().clone();
    assert_eq!(
        add(
            &mut submitted,
            Term::Identity {
                space: changed.space()
            }
        ),
        identity
    );
    assert_eq!(add(&mut submitted, Term::X), logical);
    assert_eq!(changed.implementation(), expected.implementation);
    let error = changed
        .check(
            &submitted,
            &[ProofRule::ExactLeaf { contract: expected }],
            ProofId(0),
            &required,
            Limits::default(),
        )
        .unwrap_err();
    assert!(
        matches!(error, AdapterError::Kernel(message) if message.contains("frozen required contract"))
    );
}

#[test]
fn an_imported_requirement_allows_additional_proof_terms() {
    let imported = import_raw(raw(
        vec![port(0, &[4])],
        vec![gate(SingleGate::Z, 0, 1)],
        &[1],
    ))
    .unwrap();
    let mut graph = imported.graph().clone();
    let identity = add(
        &mut graph,
        Term::Identity {
            space: imported.space(),
        },
    );
    let logical = add(&mut graph, Term::Z);
    let expected = Contract {
        implementation: imported.implementation(),
        input_encoding: identity,
        output_encoding: identity,
        logical,
    };
    let required = RequiredContract::new(graph.clone(), expected);
    let proof_z = add(&mut graph, Term::Z);
    let producer_claim = Contract {
        logical: proof_z,
        ..expected
    };
    imported
        .check(
            &graph,
            &[ProofRule::ExactLeaf {
                contract: producer_claim,
            }],
            ProofId(0),
            &required,
            Limits::default(),
        )
        .unwrap();
}
