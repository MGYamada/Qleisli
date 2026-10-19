//! Independent small rectangular equations; no sampled state is an oracle.
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
use qleisli::interchange::native::Proposal;
use qleisli::interchange::pure_leaf::{PureBoundary, check_pure};
use qleisli::interchange::{RootInterface, Version};
use qleisli::ir::*;
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::Arc;

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
    }
}

fn raw(input: QuantumPort, operations: Vec<RawOp>, output: u32) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![input],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![TokenId(output)],
        classical_outputs: vec![],
        declared_effect: Effect::Isometry,
    }
}

fn preparation() -> RawProgram {
    raw(
        port(0, &[]),
        vec![
            RawOp::UnpackUnit { input: TokenId(0) },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(7),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(1),
                output: TokenId(2),
            },
        ],
        2,
    )
}

fn boundary() -> PureBoundary {
    PureBoundary::new(BasisType::Unit, BasisType::Bit, port(0, &[]), port(2, &[7])).unwrap()
}

fn plus() -> Matrix {
    Matrix::new(2, 1, vec![Exact::inv_sqrt2(); 2]).unwrap()
}

fn proposal(raw: &RawProgram, boundary: &PureBoundary, version: Version) -> Vec<u8> {
    Proposal::from_raw(
        raw,
        Some(&RootInterface {
            input: boundary.domain().clone(),
            output: boundary.codomain().clone(),
        }),
        version,
        None,
    )
    .unwrap()
    .artifact()
    .to_vec()
}

fn check(raw: &RawProgram, boundary: &PureBoundary, meaning: &Matrix) -> bool {
    check_pure(
        qleisli::edition::Edition::E2026,
        &proposal(raw, boundary, Version::V2),
        boundary,
        meaning,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .is_ok()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_preparation_and_complete_receipt_binding() {
    for version in [Version::V1, Version::V2] {
        let raw = preparation();
        let boundary = boundary();
        let mut bytes = proposal(&raw, &boundary, version);
        let matrix = plus();
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let checked = check_pure(
            qleisli::edition::Edition::E2026,
            &bytes,
            &boundary,
            &matrix,
            &mut budget,
        )
        .unwrap();
        assert_eq!(checked.program().raw(), &raw);
        assert_eq!(checked.meaning(), &matrix);
        assert_eq!(checked.boundary(), &boundary);
        assert_eq!(
            checked.exact_work(),
            DEFAULT_EXACT_WORK - budget.remaining()
        );
        assert!(checked.exact_work() > 0);
        assert!(checked.matches(&bytes, &boundary, &matrix));
        let exported = qleisli::interchange::export(
            checked.program(),
            Some(&RootInterface {
                input: BasisType::Unit,
                output: BasisType::Bit,
            }),
            version,
        )
        .unwrap();
        check_pure(
            qleisli::edition::Edition::E2026,
            &exported,
            &boundary,
            &matrix,
            &mut budget,
        )
        .unwrap();
        bytes.push(b' ');
        assert!(!checked.matches(&bytes, &boundary, &matrix));
        check_pure(
            qleisli::edition::Edition::E2026,
            &bytes,
            &boundary,
            &matrix,
            &mut budget,
        )
        .unwrap();
    }
}

#[test]
fn phase_and_nonisometric_requests_are_not_preparation_evidence() {
    let minus = Exact::inv_sqrt2().neg().unwrap();
    for entries in [
        vec![minus; 2],
        vec![Exact::one(); 2],
        vec![Exact::zero(); 2],
        vec![Exact::inv_sqrt2(), minus],
    ] {
        assert!(!check(
            &preparation(),
            &boundary(),
            &Matrix::new(2, 1, entries).unwrap()
        ));
    }
    // The right matrix must not survive a changed implementation.
    let mut replaced = preparation();
    replaced.operations[2] = RawOp::Gate {
        gate: SingleGate::X,
        input: TokenId(1),
        output: TokenId(2),
    };
    assert!(!check(&replaced, &boundary(), &plus()));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn distinct_equal_width_type_trees_and_zero_width_owners() {
    let domain = BasisType::pair(BasisType::Unit, BasisType::Bit);
    let boundary = PureBoundary::new(domain, BasisType::Bit, port(0, &[7]), port(2, &[7])).unwrap();
    let mut raw = raw(
        port(0, &[7]),
        vec![
            RawOp::Split {
                input: TokenId(0),
                left: TokenId(1),
                right: TokenId(2),
                left_bits: 0,
            },
            RawOp::UnpackUnit { input: TokenId(1) },
        ],
        2,
    );
    raw.declared_effect = Effect::Unitary;
    let identity = Matrix::identity(2).unwrap();
    assert!(check(&raw, &boundary, &identity));
    let bytes = proposal(&raw, &boundary, Version::V2);
    let wrong_tree =
        PureBoundary::new(BasisType::Bit, BasisType::Bit, port(0, &[7]), port(2, &[7])).unwrap();
    assert!(
        check_pure(
            qleisli::edition::Edition::E2026,
            &bytes,
            &wrong_tree,
            &identity,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .is_err()
    );
    raw.operations.pop(); // Zero physical width does not discharge an owner.
    assert!(!check(&raw, &boundary, &identity));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn preparation_tensor_preserves_axes_and_every_input_column() {
    let domain = BasisType::Bit;
    let codomain = BasisType::pair(BasisType::Bit, BasisType::Bit);
    let boundary = PureBoundary::new(domain, codomain, port(0, &[19]), port(3, &[7, 19])).unwrap();
    let raw = raw(
        port(0, &[19]),
        vec![
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(7),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(1),
                output: TokenId(2),
            },
            RawOp::Join {
                left: TokenId(2),
                right: TokenId(0),
                output: TokenId(3),
            },
        ],
        3,
    );
    let h = Exact::inv_sqrt2();
    let z = Exact::zero();
    // First tuple field is the low axis: |x> maps to |+> tensor |x>.
    let matrix = Matrix::new(4, 2, vec![h, z, h, z, z, h, z, h]).unwrap();
    assert!(check(&raw, &boundary, &matrix));
    let swapped = Matrix::new(4, 2, vec![h, z, z, h, h, z, z, h]).unwrap();
    assert!(!check(&raw, &boundary, &swapped));
    let wrong_order = PureBoundary::new(
        boundary.domain().clone(),
        boundary.codomain().clone(),
        port(0, &[19]),
        port(3, &[19, 7]),
    )
    .unwrap();
    let bytes = proposal(&raw, &boundary, Version::V2);
    assert!(
        check_pure(
            qleisli::edition::Edition::E2026,
            &bytes,
            &wrong_order,
            &matrix,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .is_err()
    );
}

#[test]
fn observation_cannot_be_hidden_behind_pure_effects_or_unreturned_results() {
    for effect in [Effect::Unitary, Effect::Isometry, Effect::Observe] {
        let mut observed = preparation();
        observed.declared_effect = effect;
        observed.operations.extend([
            RawOp::Init0 {
                output: TokenId(3),
                wire: WireId(11),
            },
            RawOp::MeasureZ {
                input: TokenId(3),
                output: ClassicalId(0),
            },
        ]);
        assert!(!check(&observed, &boundary(), &plus()));
        observed.operations.pop();
        observed
            .operations
            .push(RawOp::Discard { input: TokenId(3) });
        assert!(!check(&observed, &boundary(), &plus()));
        let mut reset = preparation();
        reset.declared_effect = effect;
        reset.operations.push(RawOp::Reset {
            input: TokenId(2),
            output: TokenId(4),
            fresh_wire: WireId(11),
        });
        reset.quantum_outputs = vec![TokenId(4)];
        let b = PureBoundary::new(
            BasisType::Unit,
            BasisType::Bit,
            port(0, &[]),
            port(4, &[11]),
        )
        .unwrap();
        let zero = Matrix::new(2, 1, vec![Exact::one(), Exact::zero()]).unwrap();
        assert!(!check(&reset, &b, &zero));
    }
}

#[test]
fn mismatched_ports_dimensions_and_exhausted_budgets_fail_closed() {
    let b = boundary();
    let bytes = proposal(&preparation(), &b, Version::V2);
    for (input, output) in [
        (port(9, &[]), port(2, &[7])),
        (port(0, &[]), port(8, &[7])),
        (port(0, &[]), port(2, &[9])),
    ] {
        let wrong = PureBoundary::new(BasisType::Unit, BasisType::Bit, input, output).unwrap();
        assert!(
            check_pure(
                qleisli::edition::Edition::E2026,
                &bytes,
                &wrong,
                &plus(),
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_err()
        );
    }
    assert!(
        check_pure(
            qleisli::edition::Edition::E2026,
            &bytes,
            &b,
            &Matrix::identity(2).unwrap(),
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .is_err()
    );
    for work in [0, 1, DEFAULT_EXACT_WORK + 1] {
        assert!(
            check_pure(
                qleisli::edition::Edition::E2026,
                &bytes,
                &b,
                &plus(),
                &mut Budget::new(work)
            )
            .is_err()
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn every_native_request_is_decoded_strictly_again() {
    let b = boundary();
    let bytes = proposal(&preparation(), &b, Version::V2);
    let checked = check_pure(
        qleisli::edition::Edition::E2026,
        &bytes,
        &b,
        &plus(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    let request = std::str::from_utf8(checked.program().request().unwrap()).unwrap();
    let requests = [
        request.to_owned(),
        request.replacen('{', "{\"producer_accepted\":true,", 1),
        request.replace("\"kind\":\"pure-leaf\"", "\"kind\":\"leaf\""),
        request.replace("\"version\":1", "\"version\":99"),
        request.replace("qleisli.native-contract", "qleisli.unknown-contract"),
        request.replace("\"rows\":2", "\"rows\":1"),
        String::new(),
    ];
    for (index, request) in requests.iter().enumerate() {
        if index > 0 {
            assert_ne!(request, &requests[0]);
        }
        let mut packet = b"QLV1".to_vec();
        packet.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
        packet.extend_from_slice(&(request.len() as u32).to_le_bytes());
        packet.extend_from_slice(&bytes);
        packet.extend_from_slice(request.as_bytes());
        let mut outer = b"QLV2".to_vec();
        for field in [0u32, packet.len() as u32, 0, 0, 0] {
            outer.extend_from_slice(&field.to_le_bytes());
        }
        outer.extend_from_slice(&packet);
        let packet = outer;
        let mut child = Command::new(checked.program().checker())
            .args(["--qirf-contract", env!("CARGO_PKG_VERSION")])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(&packet).unwrap();
        let output = child.wait_with_output().unwrap();
        assert_eq!(
            output.status.success(),
            index == 0,
            "request {index}: {:?}",
            output
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn fresh_dependency_body_check_rejects_substitution_and_stale_evidence() {
    use qleisli::contract::{FunctionEvidence, FunctionIdentity};
    let mut gate = raw(
        port(0, &[7]),
        vec![RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(0),
            output: TokenId(1),
        }],
        1,
    );
    gate.declared_effect = Effect::Unitary;
    let evidence = FunctionEvidence::check(
        qleisli::edition::Edition::E2026,
        BasisType::Bit,
        gate.clone(),
        gate,
        FunctionIdentity {
            implementation: "H".into(),
            specification: "reference-H".into(),
            sources: vec![(
                "h.qli".into(),
                "unitary fn h(q: Q<Bit>) -> Q<Bit> { h(q) }".into(),
            )],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    let mut root = preparation();
    root.operations[2] = RawOp::ApplyUnitary {
        input: TokenId(1),
        output: TokenId(2),
        steps: vec![CircuitStep {
            controls: vec![],
            action: CircuitAction::Contract {
                indices: vec![0],
                evidence: Arc::new(evidence),
                adjoint: false,
            },
        }],
    };
    let bytes = proposal(&root, &boundary(), Version::V2);
    let checked = check_pure(
        qleisli::edition::Edition::E2026,
        &bytes,
        &boundary(),
        &plus(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    let text = std::str::from_utf8(&bytes).unwrap();
    assert!(text.contains("\"gate\":\"h\""));
    for altered in [
        text.replacen("\"gate\":\"h\"", "\"gate\":\"x\"", 1),
        text.replace("\"gate\":\"h\"", "\"gate\":\"x\""),
    ] {
        assert!(!checked.matches(altered.as_bytes(), &boundary(), &plus()));
        assert!(
            check_pure(
                qleisli::edition::Edition::E2026,
                altered.as_bytes(),
                &boundary(),
                &plus(),
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_err()
        );
    }
}
