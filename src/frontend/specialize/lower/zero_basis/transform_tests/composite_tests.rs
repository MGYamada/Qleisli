//! Small original-constructor controls; native tests use the actual emitted graph.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

const OTHER: &str = "unitary fn had(q:Q<Bit>)->Q<Bit>{h(q)}unitary fn id(q:Q<Bit>)->Q<Bit>{q}";

/// Keep the precise packed tree in the generic source binder and entry.
fn entry(operation: &str, pair: bool) -> String {
    let basis = if pair { "(Bit,Bit)" } else { "Bit" };
    format!(
        "{OTHER}fn invoke[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}> requires Applicable(U){{U(q)}}pub unitary fn entry(q:Q<{basis}>)->Q<{basis}>{{invoke[{operation}](q)}}"
    )
}

#[test]
fn all_original_composite_constructors_retain_structural_table_dependencies() {
    for (operation, pair) in [
        ("then_op(scalar,had)", false),
        ("tensor_op(scalar,had)", true),
        ("conjugate_op(scalar,had)", false),
        ("adjoint(then_op(scalar,had))", false),
        ("controlled(then_op(scalar,had))", true),
        ("power(then_op(scalar,had),0)", false),
        ("power(adjoint(then_op(scalar,had)),2)", false),
    ] {
        let proposal = lower(&entry(operation, pair));
        validate(&proposal).unwrap();
        check_event(&proposal, &operation_event(&proposal)).unwrap();
        assert_eq!(proposal.zero_basis.len(), 2);
        assert!(
            proposal
                .zero_basis
                .iter()
                .all(|interval| interval.input.axes.is_empty())
        );
    }
}

#[test]
fn composite_zero_width_fields_preserve_their_distinct_owner_and_basis_trees() {
    for (basis, operation) in [
        ("(Unit,Bit)", "tensor_op(zero,scalar)"),
        ("(Bits<0>,Bit)", "tensor_op(bits_zero,scalar)"),
        ("(Bit,Unit)", "tensor_op(scalar,zero)"),
    ] {
        let source = format!(
            "unitary fn zero(q:Q<Unit>)->Q<Unit>{{basis q as label {{()}}}}unitary fn bits_zero(q:Q<Bits<0>>)->Q<Bits<0>>{{basis q as label {{empty_bits()}}}}fn invoke[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}> requires Applicable(U){{U(q)}}pub unitary fn entry(q:Q<{basis}>)->Q<{basis}>{{invoke[{operation}](q)}}"
        );
        let proposal = lower(&source);
        validate(&proposal).unwrap();
        let event = operation_event(&proposal);
        check_event(&proposal, &event).unwrap();
        let graph = json::parse(&proposal.graph).unwrap();
        let defs = p::array(p::field(&graph, "definitions").unwrap()).unwrap();
        assert!(defs.iter().any(|node| {
            let body = p::field(node, "body").unwrap();
            p::tag(body).unwrap() == "structural"
                && p::tag(p::field(body, "operation").unwrap()).unwrap() == "split_tuple"
                && p::endpoints(node)
                    .unwrap()
                    .1
                    .iter()
                    .any(|port| port.axes.is_empty())
        }));
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_valid_other_constructor_trees_cannot_replace_the_original_source() {
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    for (original, replacement, pair) in [
        ("then_op(scalar,had)", "then_op(had,scalar)", false),
        ("tensor_op(scalar,had)", "tensor_op(had,scalar)", true),
        (
            "conjugate_op(scalar,had)",
            "conjugate_op(had,scalar)",
            false,
        ),
        ("adjoint(then_op(scalar,had))", "then_op(scalar,had)", false),
        ("controlled(scalar)", "tensor_op(id,scalar)", true),
        (
            "power(then_op(scalar,had),0)",
            "power(conjugate_op(scalar,had),0)",
            false,
        ),
    ] {
        let expected = lower(&entry(original, pair));
        let mut substituted = lower(&entry(replacement, pair));
        validate(&substituted).unwrap();
        // Both programs are independently valid before substituting source.
        kernel.inspect(substituted.payload()).unwrap();
        substituted.source = expected.source;
        assert!(validate(&substituted).is_err());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_execution_preserves_composite_full_phase_with_an_untouched_reference() {
    use crate::interchange::hierarchical::execution::ExecutionLimits;
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    // Numerical execution is an engineering regression. The expected matrices
    // below are written independently; no full source-preservation claim follows.
    for (operation, pair, exponent) in [
        ("then_op(scalar,scalar)", false, 2),
        ("adjoint(then_op(scalar,scalar))", false, 6),
        ("power(then_op(scalar,scalar),0)", false, 0),
        ("tensor_op(scalar,scalar)", true, 2),
        ("controlled(then_op(scalar,scalar))", true, 2),
    ] {
        let proposal = lower(&entry(operation, pair));
        validate(&proposal).unwrap();
        let checked = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let width = if pair { 2 } else { 1 };
        let input: Vec<_> = (0..(1usize << (width + 1)))
            .map(|i| [0.1 * (i + 1) as f64, -0.05 * i as f64])
            .collect();
        let actual = checked
            .execute_pure(
                &input,
                2,
                ExecutionLimits {
                    max_amplitudes: 16,
                    max_steps: 1000,
                },
            )
            .unwrap();
        let expected: Vec<_> = input
            .iter()
            .enumerate()
            .map(|(i, [re, im])| {
                let exponent = if operation.starts_with("controlled") && i & 1 == 0 {
                    0
                } else {
                    exponent
                };
                match exponent {
                    0 => [*re, *im],
                    2 => [-*im, *re],
                    6 => [*im, -*re],
                    _ => panic!("fixed exact quarter-turn expectation"),
                }
            })
            .collect();
        assert_eq!(actual.amplitudes.len(), expected.len());
        for (actual, expected) in actual
            .amplitudes
            .iter()
            .flatten()
            .zip(expected.iter().flatten())
        {
            assert!((actual - expected).abs() < 1e-12);
        }
    }
}

#[test]
fn original_composites_keep_distinct_zero_width_arrow_endpoints() {
    let conversions = "unitary fn to_bits(q:Q<Unit>)->Q<Bits<0>>{basis q as label {empty_bits()}}unitary fn to_unit(q:Q<Bits<0>>)->Q<Unit>{basis q as label {()}}";
    for (input, output, operation) in [
        ("Unit", "Unit", "then_op(to_bits,to_unit)"),
        ("Bits<0>", "Unit", "adjoint(to_bits)"),
        ("(Unit,Bit)", "(Bits<0>,Bit)", "tensor_op(to_bits,scalar)"),
    ] {
        let source = format!(
            "{conversions}fn invoke[const U:Op<{input} -> {output}>](q:Q<{input}>)->Q<{output}> requires Applicable(U){{U(q)}}pub unitary fn entry(q:Q<{input}>)->Q<{output}>{{invoke[{operation}](q)}}"
        );
        let proposal = lower(&source);
        validate(&proposal).unwrap();
        check_event(&proposal, &operation_event(&proposal)).unwrap();
        assert!(
            proposal
                .zero_basis
                .iter()
                .any(|interval| interval.input.basis != interval.output.basis)
        );
    }
}
