//! Original-plan retention and independent coordinate controls.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_and_compatibility_execution_keep_the_same_owned_plan() {
    let kernel =
        crate::interchange::hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let artifact = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/",
        "tests/fixtures/verification_v022/hierarchy/h.qirh"
    ));
    let request = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/",
        "tests/fixtures/verification_v022/hierarchy/h.request.json"
    ));
    let input = [[1.0, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, 2.0]];
    let limits = ExecutionLimits {
        max_amplitudes: 8,
        max_steps: 1000,
    };
    let mut native = kernel.check_against_native(artifact, request).unwrap();
    let first = native.execute_pure(&input, 2, limits).unwrap();
    let address = native.execution().unwrap() as *const Plan;
    assert_eq!(address, native.execution().unwrap() as *const Plan);
    // Private fault injection: public reports expose only immutable slices.
    // Poisoning old transport storage catches any subsequent reparse, while
    // the actual execution plan must retain its original exact matrix/nodes.
    native.payload = std::sync::Arc::from(b"not JSON".as_slice());
    native.finite_indices.clear();
    let second = native.execute_pure(&input, 2, limits).unwrap();
    assert_eq!(first.amplitudes, second.amplitudes);
    assert_eq!(first.steps, second.steps);
    assert_eq!(address, native.execution().unwrap() as *const Plan);

    let mut compatibility = kernel.check_against(artifact, request).unwrap();
    let first = compatibility.execute(&input, 2, limits).unwrap();
    let address = compatibility.reconstruction.execution().unwrap() as *const Plan;
    compatibility.reconstruction.payload = std::sync::Arc::from(b"not JSON".as_slice());
    compatibility.reconstruction.leaves.clear();
    let second = compatibility.execute(&input, 2, limits).unwrap();
    assert_eq!(first.amplitudes, second.amplitudes);
    assert_eq!(first.steps, second.steps);
    assert_eq!(
        address,
        compatibility.reconstruction.execution().unwrap() as *const Plan
    );
}

#[test]
fn compilation_retains_literal_exact_phase_before_numerical_interpretation() {
    let side = r#"{"quantum":[{"owner":0,"basis":[{"tag":"bit"}],"axes":[9]}],"classical":[]}"#;
    let original = format!(
        r#"{{"definitions":[{{"interface":{{"inputs":{side},"outputs":{side}}},"effect":"unitary","body":{{"tag":"dyadic_phase","target":0,"j":9,"k":3}}}}],"entry":{{"implementation":0}}}}"#
    );
    let actual = json::parse(original.as_bytes()).unwrap();
    let program = Program::compile(&actual, BTreeMap::new()).unwrap();
    assert!(matches!(
        program.nodes[0].op,
        Op::Phase {
            target: 0,
            j: 9,
            k: 3
        }
    ));
    let result = execute_pure(
        &program,
        &[[0.0, 0.0], [1.0, 0.0]],
        1,
        ExecutionLimits {
            max_amplitudes: 4,
            max_steps: 10,
        },
    )
    .unwrap();
    let r = std::f64::consts::FRAC_1_SQRT_2;
    assert!((result.amplitudes[1][0] - r).abs() < 1e-15);
    assert!((result.amplitudes[1][1] - r).abs() < 1e-15);
}

#[test]
fn prepared_and_readout_positions_retain_order_and_reference_coefficients() {
    // A hand-authored untrusted materialization control, not native acceptance.
    // Input axes [9,3], fresh zero axis 7; circuit output order [9,7,3].
    // Observe fresh 7 then data 9; pack order is [20,21], residual axis is 3.
    let input = r#"{"quantum":[{"owner":0,"axes":[9]},{"owner":1,"axes":[3]}],"classical":[]}"#;
    let prepared = r#"{"quantum":[{"owner":0,"axes":[9]},{"owner":1,"axes":[3]},{"owner":2,"axes":[7]}],"classical":[]}"#;
    let after_first =
        r#"{"quantum":[{"owner":0,"axes":[9]},{"owner":1,"axes":[3]}],"classical":[]}"#;
    let residual = r#"{"quantum":[{"owner":1,"axes":[3]}],"classical":[]}"#;
    let original = format!(
        r#"{{"preparation":{{"initializations":[{{"interface":{{"inputs":{input},"outputs":{prepared}}},"body":{{"tag":"init0","output":2}}}}]}},"readout":{{"measurements":[{{"interface":{{"inputs":{prepared}}},"body":{{"tag":"observe_z","input":2,"output":20}}}},{{"interface":{{"inputs":{after_first}}},"body":{{"tag":"observe_z","input":0,"output":21}}}}],"pack":[20,21],"outputs":{residual}}}}}"#
    );
    let program = Program {
        nodes: vec![Node {
            width: 3,
            op: Op::Permutation(vec![0, 2, 1]),
        }],
        root: 0,
        inputs: vec![9, 3, 7],
        outputs: vec![9, 7, 3],
    };
    let actual = json::parse(original.as_bytes()).unwrap();
    let plan = InstrumentPlan::compile(&actual, program).unwrap();
    assert_eq!(plan.fresh_axes, [7]);
    assert_eq!(plan.input_positions, [0, 1]);
    assert_eq!(plan.measurements, [(20, 7), (21, 9)]);
    assert_eq!(plan.pack, [20, 21]);
    assert_eq!(plan.outcome_positions, [1, 0]);
    assert_eq!(plan.residual_positions, [2]);
    let input = [
        [1.0, 0.0],
        [2.0, 0.0],
        [0.0, 3.0],
        [0.0, 4.0],
        [5.0, 0.0],
        [6.0, 0.0],
        [0.0, 7.0],
        [0.0, 8.0],
    ];
    let result = execute_instrument(
        &plan,
        &input,
        2,
        ExecutionLimits {
            max_amplitudes: 32,
            max_steps: 100,
        },
    )
    .unwrap();
    assert_eq!(
        result.branches,
        vec![
            vec![[1.0, 0.0], [0.0, 3.0], [5.0, 0.0], [0.0, 7.0]],
            vec![[0.0, 0.0]; 4],
            vec![[2.0, 0.0], [0.0, 4.0], [6.0, 0.0], [0.0, 8.0]],
            vec![[0.0, 0.0]; 4],
        ]
    );
    assert_eq!(result.steps, 52);
}
