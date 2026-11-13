//! Issue #521: the intended operator is independent of either implementation.
//! These finite regressions are not a source-preservation theorem.

use super::{Exact, SourceRoot, apply_steps, compile_project, operator};
use qleisli::contract::exact::{Budget, Exact as NativeExact, Matrix};
use qleisli::contract::{
    BasisType, CheckedContract, Circuit, Contract, ContractError, DEFAULT_EXACT_WORK, Encoding,
};
use qleisli::ir::{CircuitStep, RawOp};
use std::{fs, path::Path};

const POSITIVE: &str = "qualtran/qrom2_qmatch";
const FAULTS: [&str; 2] = [
    "semantic_faults/qrom2_qmatch_wrong_arm",
    "semantic_faults/qrom2_qmatch_arm_phase",
];

// Row/column bits are (a0,a1,t0,t1), with the first leaf least significant.
// This definition reads no source, compiler table, native response or circuit.
fn output(column: usize) -> usize {
    let address = column % 4;
    let target = column / 4;
    address + 4 * (target ^ [1, 2, 3, 0][address])
}

fn expected() -> Vec<Vec<Exact>> {
    (0..16)
        .map(|row| {
            (0..16)
                .map(|col| {
                    if row == output(col) {
                        Exact::ONE
                    } else {
                        Exact::ZERO
                    }
                })
                .collect()
        })
        .collect()
}

fn source(project: &str) -> String {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus");
    let selected = if project == "qualtran/qrom2" {
        // Follow the same recorded migration chain as maintained discovery.
        let result = std::process::Command::new("python3")
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .args(["-B", "-c", "import sys;sys.path.insert(0,'scripts');from check_input_corpus import current_project;print(current_project({'project':'qualtran/qrom2'}))"])
            .output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        std::path::PathBuf::from(String::from_utf8(result.stdout).unwrap().trim())
    } else {
        corpus.join(project)
    };
    fs::read_to_string(selected.join("kernel.qli")).unwrap()
}

fn steps(definitions: &str, name: &str) -> Vec<CircuitStep> {
    // power(_,1) requests the complete open operation. Zero preparation here
    // never becomes the oracle: every column of the retained circuit is checked.
    let root = SourceRoot::new(
        "observe fn main() -> Unit {\n\
        let q = join(join(join(init0(),init0()),init0()),init0());\n\
        let q = power(kernel::kernel,1)(q); discard(q); ()\n}",
    );
    root.write("kernel.qli", definitions);
    let checked = compile_project(&root.0).expect("valid source must pass fresh native checking");
    // Optional reproducibility output, never an input or an acceptance receipt.
    if let Some(directory) = std::env::var_os("QLEISLI_QROM_EVIDENCE_DIR") {
        let directory = Path::new(&directory).join(name.replace('/', "_"));
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("kernel.qli"), definitions).unwrap();
        fs::copy(root.0.join("main.qli"), directory.join("main.qli")).unwrap();
        fs::copy(root.0.join("Qargo.toml"), directory.join("Qargo.toml")).unwrap();
        fs::write(directory.join("accepted-ir.json"), checked.artifact()).unwrap();
        if let Some(request) = checked.request() {
            fs::write(directory.join("source-request.json"), request).unwrap();
        }
    }
    let circuits: Vec<_> = checked
        .program()
        .operations
        .iter()
        .filter_map(|op| {
            if let RawOp::ApplyUnitary { steps, .. } = op {
                Some(steps.clone())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(circuits.len(), 1, "the complete kernel must be retained");
    circuits.into_iter().next().unwrap()
}

fn requested_check(steps: Vec<CircuitStep>) -> Result<CheckedContract, ContractError> {
    // The native checker receives all 256 exact coefficients. No comparison
    // with qrom2, sampled probabilities or equality modulo phase authorizes it.
    let basis = (1..4).fold(BasisType::Bit, |a, _| BasisType::pair(a, BasisType::Bit));
    let matrix = Matrix::new(
        16,
        16,
        (0..16)
            .flat_map(|row| {
                (0..16).map(move |col| NativeExact::integer(i128::from(row == output(col))))
            })
            .collect(),
    )
    .unwrap();
    let encoding = Encoding::identity(basis.clone()).unwrap();
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let contract = Contract::new(encoding.clone(), encoding, matrix, &mut budget).unwrap();
    CheckedContract::check(
        qleisli::edition::Edition::E2026,
        Circuit::new(basis, steps).unwrap(),
        contract,
        &mut budget,
    )
}

#[test]
fn qmatch_qrom_oracle_pins_all_ordered_outputs() {
    // Literal independent cross-check of the integer convention.
    assert_eq!(
        (0..16).map(output).collect::<Vec<_>>(),
        [4, 9, 14, 3, 0, 13, 10, 7, 12, 1, 6, 11, 8, 5, 2, 15]
    );
    for col in 0..16 {
        assert_eq!(output(col) % 4, col % 4);
        assert_eq!(output(output(col)), col);
    }
    let text = source(POSITIVE);
    let positions: Vec<_> = ["3 => keep", "1 => load2", "0 => load1", "2 => load3"]
        .iter()
        .map(|arm| text.find(arm).unwrap())
        .collect();
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn qmatch_qrom_complete_matrix_and_explicit_circuit_match_independent_oracle() {
    let wanted = expected();
    for project in [POSITIVE, "qualtran/qrom2"] {
        let circuit = steps(&source(project), project);
        assert_eq!(
            operator(4, &circuit),
            wanted,
            "all exact entries: {project}"
        );
        requested_check(circuit).expect("native full-matrix equation must hold");
        println!("{project}: all 256 exact entries and native requested equation passed");
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn qmatch_qrom_valid_wrong_arm_and_phase_are_semantic_rejections() {
    let wanted = expected();
    for project in FAULTS {
        let circuit = steps(&source(project), project);
        let actual = operator(4, &circuit);
        assert_ne!(
            actual, wanted,
            "mutation escaped independent oracle: {project}"
        );
        if project.ends_with("arm_phase") {
            // Every computational-basis probability agrees. Exact +1 matters.
            for row in 0..16 {
                for col in 0..16 {
                    assert_eq!(
                        actual[row][col] * actual[row][col].conjugate(),
                        wanted[row][col] * wanted[row][col].conjugate()
                    );
                }
            }
            assert_eq!(actual[3][3], Exact::phase(1));
        } else {
            assert_eq!(actual[5][1], Exact::ONE);
            assert_eq!(wanted[9][1], Exact::ONE);
        }
        assert_eq!(
            requested_check(circuit).unwrap_err(),
            ContractError::EquationMismatch,
            "must not be parser, owner, unavailable-profile or capacity rejection: {project}"
        );
        let differences = (0..16)
            .flat_map(|row| (0..16).map(move |col| (row, col)))
            .filter(|&(row, col)| actual[row][col] != wanted[row][col])
            .count();
        println!(
            "{project}: valid source; {differences} differing exact entries; native EquationMismatch"
        );
    }
    // A scalar on the entire correct source must also fail, even though its
    // channel agrees. This guards against silently weakening to phase quotients.
    let global = source(POSITIVE).replace(
        "join(join(join(a0, a1), t0), t1)",
        "global_phase_eighth(join(join(join(a0, a1), t0), t1))",
    );
    assert_eq!(
        requested_check(steps(&global, "global_phase")).unwrap_err(),
        ContractError::EquationMismatch
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn qmatch_qrom_exact_coherence_and_external_reference_correlations() {
    let circuit = steps(&source(POSITIVE), "coherence");
    // Dense normalized state with real/imaginary relative phases, every address
    // and every target. Exact arithmetic has no tolerance or phase alignment.
    let input: Vec<_> = (0..16)
        .map(|i| Exact::new([1, 0, 0, 0], 2) * Exact::phase(i % 8))
        .collect();
    let mut actual = input.clone();
    apply_steps(&mut actual, &circuit, &[0, 1, 2, 3], 0);
    let mut wanted = vec![Exact::ZERO; 16];
    for col in 0..16 {
        wanted[output(col)] = input[col];
    }
    assert_eq!(actual, wanted);

    // Choi vector sum_x |x>_S |x>_R / 4: a purely algebraic extension of the
    // four-qubit checked circuit. No eight-qubit source/request is generated.
    // Its full ordered amplitudes test all reference correlations; U=oracle
    // additionally implies U tensor I_E=oracle tensor I_E for every reference E.
    let mut choi = vec![Exact::ZERO; 256];
    let mut expected_choi = vec![Exact::ZERO; 256];
    for col in 0..16 {
        choi[col + 16 * col] = Exact::new([1, 0, 0, 0], 2);
        expected_choi[output(col) + 16 * col] = Exact::new([1, 0, 0, 0], 2);
    }
    apply_steps(&mut choi, &circuit, &[0, 1, 2, 3], 0);
    assert_eq!(choi, expected_choi);
}
