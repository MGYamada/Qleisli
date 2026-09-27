use super::*;

// These local fixtures have no external producer; freeze their full expected
// graph immediately. Trust-boundary regressions below freeze first and invoke
// super::check after making adversarial edits to a separate submitted graph.
fn check(
    graph: &TermGraph,
    proofs: &[ProofRule],
    root: ProofId,
    expected: &Contract,
    limits: Limits,
) -> Result<CheckedEvidence, KernelError> {
    let required = RequiredContract::new(graph.clone(), *expected);
    super::check(graph, proofs, root, &required, limits)
}

struct Fixture {
    graph: TermGraph,
    unit: TypeId,
    bit: TypeId,
    pair: TypeId,
}

impl Fixture {
    fn new() -> Self {
        Self {
            graph: TermGraph {
                types: vec![
                    TypeNode::Unit,
                    TypeNode::Bit,
                    TypeNode::Pair {
                        low: TypeId(1),
                        high: TypeId(1),
                    },
                ],
                terms: vec![],
            },
            unit: TypeId(0),
            bit: TypeId(1),
            pair: TypeId(2),
        }
    }
    fn ty(&mut self, node: TypeNode) -> TypeId {
        let id = TypeId(self.graph.types.len());
        self.graph.types.push(node);
        id
    }
    fn term(&mut self, node: Term) -> TermId {
        let id = TermId(self.graph.terms.len());
        self.graph.terms.push(node);
        id
    }
    fn id(&mut self, space: TypeId) -> TermId {
        self.term(Term::Identity { space })
    }
    fn seq(&mut self, first: TermId, second: TermId) -> TermId {
        self.term(Term::Sequence { first, second })
    }
    fn tensor(&mut self, low: TermId, high: TermId) -> TermId {
        self.term(Term::Tensor { low, high })
    }
    fn register(&mut self, exponent: usize) -> TypeId {
        let mut space = self.bit;
        for _ in 0..exponent {
            space = self.ty(TypeNode::Pair {
                low: space,
                high: space,
            });
        }
        space
    }
    fn leaf(&self, contract: Contract) -> Result<CheckedEvidence, KernelError> {
        check(
            &self.graph,
            &[ProofRule::ExactLeaf { contract }],
            ProofId(0),
            &contract,
            Limits::default(),
        )
    }
    fn encoded_z(&mut self) -> (Contract, Contract) {
        let id = self.id(self.bit);
        let z = self.term(Term::Z);
        let encoding = self.term(Term::ZeroExtend {
            logical: self.bit,
            scratch: self.bit,
        });
        let direct = self.tensor(z, id);
        let cnot = self.term(Term::Cnot);
        let phase_aux = self.tensor(id, z);
        let compute_phase = self.seq(cnot, phase_aux);
        let indirect = self.seq(compute_phase, cnot);
        (
            contract(direct, encoding, z),
            contract(indirect, encoding, z),
        )
    }
}

fn contract(implementation: TermId, encoding: TermId, logical: TermId) -> Contract {
    Contract {
        implementation,
        input_encoding: encoding,
        output_encoding: encoding,
        logical,
    }
}

#[test]
fn direct_and_compute_phase_uncompute_share_the_fixed_z_contract() {
    let mut f = Fixture::new();
    let (direct, indirect) = f.encoded_z();
    for c in [direct, indirect] {
        let checked = f.leaf(c).unwrap();
        assert_eq!(checked.contract().logical, direct.logical);
        assert_eq!(checked.contract().input_encoding, direct.input_encoding);
        assert_eq!(checked.stats().largest_matrix_dimension, 4);
        assert!(checked.stats().exact_work_used > 0);
        checked
            .check_binding(&f.graph, &RequiredContract::new(f.graph.clone(), c))
            .unwrap();
    }
}

#[test]
fn exact_encoding_checks_all_output_rows_and_rejects_auxiliary_leakage() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let x = f.term(Term::X);
    let encoding = f.term(Term::ZeroExtend {
        logical: f.bit,
        scratch: f.bit,
    });
    let bad = f.tensor(id, x);
    assert_eq!(
        f.leaf(contract(bad, encoding, id)).unwrap_err(),
        KernelError::EquationMismatch
    );
}

#[test]
fn framed_64_and_128_bit_references_do_not_allocate_global_matrices() {
    for exponent in [6, 7] {
        let mut f = Fixture::new();
        let (_, local) = f.encoded_z();
        let reference_type = f.register(exponent);
        let reference = f.id(reference_type);
        let u = f.tensor(local.implementation, reference);
        let encoding = f.tensor(local.input_encoding, reference);
        let logical = f.tensor(local.logical, reference);
        let expected = contract(u, encoding, logical);
        let proof = [
            ProofRule::ExactLeaf { contract: local },
            ProofRule::Identity {
                encoding: reference,
            },
            ProofRule::Tensor {
                low: ProofId(0),
                high: ProofId(1),
            },
        ];
        let checked = check(&f.graph, &proof, ProofId(2), &expected, Limits::default()).unwrap();
        assert_eq!(checked.stats().exact_leaves, 1);
        assert_eq!(checked.stats().largest_matrix_dimension, 4);
        assert_eq!(checked.stats().proof_nodes, 3);
    }
}

#[test]
fn shared_proof_dag_composes_without_expanding_the_circuit_or_matrices() {
    let mut f = Fixture::new();
    let (_, mut expected) = f.encoded_z();
    let mut proofs = vec![ProofRule::ExactLeaf { contract: expected }];
    for previous in 0..40 {
        expected.implementation = f.seq(expected.implementation, expected.implementation);
        expected.logical = f.seq(expected.logical, expected.logical);
        proofs.push(ProofRule::Sequence {
            first: ProofId(previous),
            second: ProofId(previous),
        });
    }
    let checked = check(&f.graph, &proofs, ProofId(40), &expected, Limits::default()).unwrap();
    assert_eq!(checked.stats().exact_leaves, 1);
    assert_eq!(checked.stats().largest_matrix_dimension, 4);
    assert!(checked.stats().term_nodes < 150);
    assert!(checked.stats().work_used < 20_000);
}

#[test]
fn same_dimension_different_middle_encodings_cannot_be_composed() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let z = f.term(Term::Z);
    let twice = f.seq(id, id);
    let expected = Contract {
        implementation: twice,
        input_encoding: id,
        output_encoding: z,
        logical: twice,
    };
    let proofs = [
        ProofRule::Identity { encoding: id },
        ProofRule::Identity { encoding: z },
        ProofRule::Sequence {
            first: ProofId(0),
            second: ProofId(1),
        },
    ];
    assert!(matches!(
        check(&f.graph, &proofs, ProofId(2), &expected, Limits::default()),
        Err(KernelError::RuleMismatch(_))
    ));
}

#[test]
fn unit_factors_are_not_silently_erased_from_encoding_domains() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let init = f.term(Term::Init0);
    let encoding = f.tensor(id, init);
    let z = f.term(Term::Z);
    let physical = f.tensor(z, id);
    assert!(matches!(
        f.leaf(contract(physical, encoding, z)),
        Err(KernelError::TypeMismatch(_))
    ));
}

#[test]
fn zero_bit_phase_is_preserved_and_control_makes_it_relative() {
    let mut f = Fixture::new();
    let id = f.id(f.unit);
    let minus = f.term(Term::Phase {
        space: f.unit,
        eighths: 4,
    });
    assert_eq!(
        f.leaf(contract(minus, id, id)).unwrap_err(),
        KernelError::EquationMismatch
    );
    f.leaf(contract(minus, id, minus)).unwrap();
    let controlled = f.term(Term::Controlled { operand: minus });
    let control_type = f.ty(TypeNode::Pair {
        low: f.bit,
        high: f.unit,
    });
    let control_id = f.id(control_type);
    assert_eq!(
        f.leaf(contract(controlled, control_id, control_id))
            .unwrap_err(),
        KernelError::EquationMismatch
    );
}

#[test]
fn tensor_order_is_low_left_and_not_interchangeable() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let z = f.term(Term::Z);
    let left = f.tensor(z, id);
    let right = f.tensor(id, z);
    let encoding = f.id(f.pair);
    assert_eq!(
        f.leaf(contract(left, encoding, right)).unwrap_err(),
        KernelError::EquationMismatch
    );
}

#[test]
fn control_adjoint_and_repetition_reuse_the_checked_local_contract() {
    let mut f = Fixture::new();
    let (_, local) = f.encoded_z();
    let id_bit = f.id(f.bit);
    let controlled = contract(
        f.term(Term::Controlled {
            operand: local.implementation,
        }),
        f.tensor(id_bit, local.input_encoding),
        f.term(Term::Controlled {
            operand: local.logical,
        }),
    );
    let adjoint = contract(
        f.term(Term::Adjoint {
            operand: controlled.implementation,
        }),
        controlled.input_encoding,
        f.term(Term::Adjoint {
            operand: controlled.logical,
        }),
    );
    let repeated = contract(
        f.term(Term::Repeat {
            operand: adjoint.implementation,
            count: u64::MAX,
        }),
        adjoint.input_encoding,
        f.term(Term::Repeat {
            operand: adjoint.logical,
            count: u64::MAX,
        }),
    );
    let proof = [
        ProofRule::ExactLeaf { contract: local },
        ProofRule::Control {
            premise: ProofId(0),
        },
        ProofRule::Adjoint {
            premise: ProofId(1),
        },
        ProofRule::Repeat {
            premise: ProofId(2),
            count: u64::MAX,
        },
    ];
    let checked = check(&f.graph, &proof, ProofId(3), &repeated, Limits::default()).unwrap();
    assert_eq!(checked.stats().exact_leaves, 1);
    assert_eq!(checked.stats().largest_matrix_dimension, 4);
}

#[test]
fn control_requires_the_same_encoding_not_only_the_same_dimensions() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let z = f.term(Term::Z);
    let leaf = Contract {
        implementation: z,
        input_encoding: id,
        output_encoding: z,
        logical: id,
    };
    f.leaf(leaf).unwrap();
    let proof = [
        ProofRule::ExactLeaf { contract: leaf },
        ProofRule::Control {
            premise: ProofId(0),
        },
    ];
    assert!(matches!(
        check(&f.graph, &proof, ProofId(1), &leaf, Limits::default()),
        Err(KernelError::RuleMismatch(_))
    ));
}

#[test]
fn adjoint_cannot_turn_preparation_into_unconditional_release() {
    let mut f = Fixture::new();
    let id = f.id(f.unit);
    let init = f.term(Term::Init0);
    let leaf = Contract {
        implementation: init,
        input_encoding: id,
        output_encoding: init,
        logical: id,
    };
    f.leaf(leaf).unwrap();
    let proof = [
        ProofRule::ExactLeaf { contract: leaf },
        ProofRule::Adjoint {
            premise: ProofId(0),
        },
    ];
    assert!(matches!(
        check(&f.graph, &proof, ProofId(1), &leaf, Limits::default()),
        Err(KernelError::TypeMismatch(_))
    ));
}

#[test]
fn adjoint_requires_logical_unitarity_even_when_the_implementation_is_unitary() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let init = f.term(Term::Init0);
    // I₂ |0> = I₂ |0> is a valid encoded equation with a unitary physical
    // implementation. The proposed inverse would assert I₂ = |0><0|.
    let leaf = Contract {
        implementation: id,
        input_encoding: init,
        output_encoding: id,
        logical: init,
    };
    f.leaf(leaf).unwrap();
    let proof = [
        ProofRule::ExactLeaf { contract: leaf },
        ProofRule::Adjoint {
            premise: ProofId(0),
        },
    ];
    assert_eq!(
        check(&f.graph, &proof, ProofId(1), &leaf, Limits::default()).unwrap_err(),
        KernelError::TypeMismatch("adjoint requires a known unitary operand")
    );
}

#[test]
fn non_hermitian_control_adjoint_and_repeat_match_explicit_phase_operators() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let t = f.term(Term::T);
    let encoding = f.term(Term::ZeroExtend {
        logical: f.bit,
        scratch: f.bit,
    });
    let local = contract(f.tensor(t, id), encoding, t);
    let controlled = contract(
        f.term(Term::Controlled {
            operand: local.implementation,
        }),
        f.tensor(id, encoding),
        f.term(Term::Controlled { operand: t }),
    );
    let inverse = contract(
        f.term(Term::Adjoint {
            operand: controlled.implementation,
        }),
        controlled.input_encoding,
        f.term(Term::Adjoint {
            operand: controlled.logical,
        }),
    );
    let expected = contract(
        f.term(Term::Repeat {
            operand: inverse.implementation,
            count: 3,
        }),
        inverse.input_encoding,
        f.term(Term::Repeat {
            operand: inverse.logical,
            count: 3,
        }),
    );
    let proof = [
        ProofRule::ExactLeaf { contract: local },
        ProofRule::Control {
            premise: ProofId(0),
        },
        ProofRule::Adjoint {
            premise: ProofId(1),
        },
        ProofRule::Repeat {
            premise: ProofId(2),
            count: 3,
        },
    ];
    let checked = check(&f.graph, &proof, ProofId(3), &expected, Limits::default()).unwrap();
    assert_eq!(checked.stats().exact_leaves, 1);
    assert_eq!(checked.stats().largest_matrix_dimension, 4);
    // A separate bounded full equation must agree with the symbolic derivation.
    f.leaf(expected).unwrap();

    // Independently specify the complete diagonal operators: low control bit,
    // next data bit, optional high auxiliary. Only control=data=1 receives
    // exp(-3 i pi / 4). No expression recursion or matrix products define this oracle.
    let explicit = |dimension: usize| {
        let mut entries = vec![Exact::zero(); dimension * dimension];
        for label in 0..dimension {
            entries[label * dimension + label] = if label & 3 == 3 {
                Exact::phase(-3)
            } else {
                Exact::one()
            };
        }
        Matrix::new(dimension, dimension, entries).unwrap()
    };
    let mut checker = Checker::new(Limits::default());
    checker.load(&f.graph).unwrap();
    let canonical = checker.contract(expected).unwrap();
    assert_eq!(
        checker.matrix(canonical.implementation.0).unwrap(),
        explicit(8)
    );
    assert_eq!(checker.matrix(canonical.logical.0).unwrap(), explicit(4));

    let wrong_phase = f.term(Term::Repeat {
        operand: controlled.logical,
        count: 3,
    });
    assert_eq!(
        f.leaf(contract(
            expected.implementation,
            expected.input_encoding,
            wrong_phase
        ))
        .unwrap_err(),
        KernelError::EquationMismatch
    );
}

#[test]
fn zero_repetition_checks_the_operand_and_the_proof() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let c = contract(id, id, id);
    let proof = [
        ProofRule::ExactLeaf { contract: c },
        ProofRule::Repeat {
            premise: ProofId(1),
            count: 0,
        },
    ];
    assert!(matches!(
        check(&f.graph, &proof, ProofId(1), &c, Limits::default()),
        Err(KernelError::InvalidGraph(_))
    ));
    let init = f.term(Term::Init0);
    f.term(Term::Repeat {
        operand: init,
        count: 0,
    });
    assert!(matches!(f.leaf(c), Err(KernelError::TypeMismatch(_))));
}

#[test]
fn zero_repetition_of_a_checked_unitary_is_a_valid_symbolic_rule() {
    let mut f = Fixture::new();
    let (_, local) = f.encoded_z();
    let expected = contract(
        f.term(Term::Repeat {
            operand: local.implementation,
            count: 0,
        }),
        local.input_encoding,
        f.term(Term::Repeat {
            operand: local.logical,
            count: 0,
        }),
    );
    let proof = [
        ProofRule::ExactLeaf { contract: local },
        ProofRule::Repeat {
            premise: ProofId(0),
            count: 0,
        },
    ];
    check(&f.graph, &proof, ProofId(1), &expected, Limits::default()).unwrap();
    f.leaf(expected).unwrap();
}

#[test]
fn implementation_and_full_graph_contents_are_bound_to_evidence() {
    let mut f = Fixture::new();
    let (direct, indirect) = f.encoded_z();
    let checked = f.leaf(direct).unwrap();
    assert_eq!(
        checked.check_binding(&f.graph, &RequiredContract::new(f.graph.clone(), indirect)),
        Err(KernelError::BindingMismatch)
    );
    assert_eq!(
        check(
            &f.graph,
            &[ProofRule::ExactLeaf { contract: direct }],
            ProofId(0),
            &indirect,
            Limits::default()
        )
        .unwrap_err(),
        KernelError::ExpectedContractMismatch
    );
    f.graph.terms[direct.logical.0] = Term::X;
    assert_eq!(
        checked.check_binding(&f.graph, &RequiredContract::new(f.graph.clone(), direct)),
        Err(KernelError::BindingMismatch)
    );
}

#[test]
fn cyclic_forward_and_dangling_graph_references_are_rejected() {
    let mut f = Fixture::new();
    let id = f.id(f.bit);
    let c = contract(id, id, id);
    for operand in [TermId(1), TermId(99)] {
        let mut graph = f.graph.clone();
        graph.terms.push(Term::Adjoint { operand });
        assert!(matches!(
            check(
                &graph,
                &[ProofRule::Identity { encoding: id }],
                ProofId(0),
                &c,
                Limits::default()
            ),
            Err(KernelError::InvalidGraph(_))
        ));
    }
    f.graph.types.push(TypeNode::Pair {
        low: TypeId(3),
        high: f.bit,
    });
    assert!(matches!(f.leaf(c), Err(KernelError::InvalidGraph(_))));
}

#[test]
fn rewiring_is_explicit_bijective_and_preserves_exact_type_shapes() {
    let mut f = Fixture::new();
    let encoding = f.id(f.pair);
    let swap = f.term(Term::Rewire {
        input: f.pair,
        output: f.pair,
        output_axes: vec![1, 0],
    });
    assert_eq!(
        f.leaf(contract(swap, encoding, encoding)).unwrap_err(),
        KernelError::EquationMismatch
    );
    let twice = f.seq(swap, swap);
    f.leaf(contract(twice, encoding, encoding)).unwrap();
    f.term(Term::Rewire {
        input: f.pair,
        output: f.pair,
        output_axes: vec![0, 0],
    });
    assert!(matches!(
        f.leaf(contract(twice, encoding, encoding)),
        Err(KernelError::InvalidGraph(_))
    ));
}

#[test]
fn invalid_phase_and_global_exact_leaf_requests_are_rejected() {
    let mut f = Fixture::new();
    let big = f.register(6);
    let id = f.id(big);
    let c = contract(id, id, id);
    assert_eq!(f.leaf(c).unwrap_err(), KernelError::LeafTooWide);
    let checked = check(
        &f.graph,
        &[ProofRule::Identity { encoding: id }],
        ProofId(0),
        &c,
        Limits::default(),
    )
    .unwrap();
    assert_eq!(checked.stats().largest_matrix_dimension, 0);
    assert_eq!(checked.stats().exact_work_used, 0);
    f.term(Term::Phase {
        space: f.unit,
        eighths: 8,
    });
    assert!(matches!(f.leaf(c), Err(KernelError::InvalidGraph(_))));
}

#[test]
fn finite_work_and_node_limits_fail_closed() {
    let mut f = Fixture::new();
    let (_, c) = f.encoded_z();
    let proof = [ProofRule::ExactLeaf { contract: c }];
    let limits = Limits {
        work: 10,
        ..Limits::default()
    };
    assert!(matches!(
        check(&f.graph, &proof, ProofId(0), &c, limits),
        Err(KernelError::Exact(ExactError::WorkLimit))
    ));
    let limits = Limits {
        max_terms: 2,
        ..Limits::default()
    };
    assert!(matches!(
        check(&f.graph, &proof, ProofId(0), &c, limits),
        Err(KernelError::Limit(_))
    ));
    let limits = Limits {
        max_proofs: 0,
        ..Limits::default()
    };
    assert!(matches!(
        check(&f.graph, &proof, ProofId(0), &c, limits),
        Err(KernelError::Limit(_))
    ));
}

#[test]
fn frozen_requirement_rejects_coordinated_meaning_edits_with_unchanged_ids() {
    let mut f = Fixture::new();
    let identity = f.id(f.bit);
    let z = f.term(Term::Z);
    let expected = contract(z, identity, z);
    let required = RequiredContract::new(f.graph.clone(), expected);
    // Both U and u still have the same IDs. A freely supplied expected Contract
    // alone would accept this new, internally consistent X = X proposition.
    f.graph.terms[z.0] = Term::X;
    assert_eq!(*required.contract(), expected);
    assert_eq!(required.graph().terms[z.0], Term::Z);
    assert_eq!(
        super::check(
            &f.graph,
            &[ProofRule::ExactLeaf { contract: expected }],
            ProofId(0),
            &required,
            Limits::default()
        )
        .unwrap_err(),
        KernelError::RequirementMismatch,
    );
}

#[test]
fn a_producer_may_append_proof_terms_without_editing_the_frozen_requirement() {
    let mut f = Fixture::new();
    let identity = f.id(f.bit);
    let z = f.term(Term::Z);
    let expected = contract(z, identity, z);
    let required = RequiredContract::new(f.graph.clone(), expected);
    let producer_z = f.term(Term::Z);
    let producer_identity = f.id(f.bit);
    let producer_claim = contract(producer_z, producer_identity, producer_z);
    let checked = super::check(
        &f.graph,
        &[ProofRule::ExactLeaf {
            contract: producer_claim,
        }],
        ProofId(0),
        &required,
        Limits::default(),
    )
    .unwrap();
    assert_eq!(checked.requirement(), &required);
    checked.check_binding(&f.graph, &required).unwrap();
    assert!(checked.graph().terms.len() > checked.requirement().graph().terms.len());
}

#[test]
fn a_valid_proof_cannot_answer_a_different_frozen_root_requirement() {
    let mut f = Fixture::new();
    let identity = f.id(f.bit);
    let z = f.term(Term::Z);
    let x = f.term(Term::X);
    let proved = contract(z, identity, z);
    let required = RequiredContract::new(f.graph.clone(), contract(x, identity, x));
    assert_eq!(
        super::check(
            &f.graph,
            &[ProofRule::ExactLeaf { contract: proved }],
            ProofId(0),
            &required,
            Limits::default()
        )
        .unwrap_err(),
        KernelError::ExpectedContractMismatch
    );
}

#[test]
fn appended_definitions_cannot_fill_holes_in_a_frozen_requirement() {
    let mut graph = TermGraph {
        types: vec![TypeNode::Unit],
        terms: vec![Term::Identity { space: TypeId(1) }],
    };
    let expected = contract(TermId(0), TermId(0), TermId(0));
    let required = RequiredContract::new(graph.clone(), expected);
    graph.types.push(TypeNode::Bit);
    assert!(matches!(
        super::check(
            &graph,
            &[ProofRule::Identity {
                encoding: TermId(0)
            }],
            ProofId(0),
            &required,
            Limits::default()
        ),
        Err(KernelError::InvalidGraph(_))
    ));

    let mut f = Fixture::new();
    let identity = f.id(f.bit);
    let expected = contract(identity, identity, TermId(1));
    let required = RequiredContract::new(f.graph.clone(), expected);
    f.id(f.bit);
    assert!(matches!(
        super::check(
            &f.graph,
            &[ProofRule::ExactLeaf { contract: expected }],
            ProofId(0),
            &required,
            Limits::default()
        ),
        Err(KernelError::InvalidGraph(_))
    ));
}

#[test]
fn adapter_matches_independent_exact_semantics_in_5425_control_and_phase_cases() {
    use qleisli_core::contract::{BasisType, Circuit};
    use qleisli_core::ir::*;

    fn compare(step: CircuitStep, cases: &mut usize) {
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![WireId(9), WireId(7), WireId(13)],
                shape: BasisShape { bits: 3 },
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![step.clone()],
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let imported = crate::adapter::import_raw(raw).unwrap();
        // This private test access does not expose a global matrix API. Every
        // imported term here has at most three bits, under ordinary leaf limits.
        let mut checker = Checker::new(Limits::default());
        checker.load(imported.graph()).unwrap();
        let actual = checker
            .matrix(checker.raw_term(imported.implementation()).unwrap())
            .unwrap();
        let basis = BasisType::pair(
            BasisType::Bit,
            BasisType::pair(BasisType::Bit, BasisType::Bit),
        );
        let expected = Circuit::new(basis, vec![step.clone()])
            .unwrap()
            .matrix(&mut Budget::new(Limits::default().work))
            .unwrap();
        assert_eq!(actual, expected, "raw step: {step:?}");
        *cases += 1;
    }

    fn controlled(action: CircuitAction, occupied: &[usize], cases: &mut usize) {
        let free: Vec<_> = (0..3).filter(|axis| !occupied.contains(axis)).collect();
        for mut code in 0..3_usize.pow(free.len() as u32) {
            let mut controls = vec![];
            for axis in &free {
                let digit = code % 3;
                code /= 3;
                if digit != 0 {
                    controls.push(BitControl {
                        index: *axis,
                        when_one: digit == 2,
                    });
                }
            }
            compare(
                CircuitStep {
                    controls: controls.clone(),
                    action: action.clone(),
                },
                cases,
            );
            if controls.len() > 1 {
                controls.reverse();
                compare(
                    CircuitStep {
                        controls,
                        action: action.clone(),
                    },
                    cases,
                );
            }
        }
    }

    let mut cases = 0;
    for target in 0..3 {
        controlled(CircuitAction::Hadamard { target }, &[target], &mut cases);
        for permutation in [vec![0, 1], vec![1, 0]] {
            for a in 0..8 {
                for b in 0..8 {
                    controlled(
                        CircuitAction::Monomial {
                            indices: vec![target],
                            permutation: permutation.clone(),
                            phases: vec![a, b],
                        },
                        &[target],
                        &mut cases,
                    );
                }
            }
        }
    }
    for phase in 0..8 {
        controlled(
            CircuitAction::Monomial {
                indices: vec![],
                permutation: vec![0],
                phases: vec![phase],
            },
            &[],
            &mut cases,
        );
    }
    for first in 0..3 {
        for second in 0..3 {
            if first != second {
                controlled(
                    CircuitAction::Monomial {
                        indices: vec![first, second],
                        permutation: vec![0, 3, 2, 1],
                        phases: vec![0; 4],
                    },
                    &[first, second],
                    &mut cases,
                );
            }
        }
    }
    assert_eq!(cases, 5425);
}
