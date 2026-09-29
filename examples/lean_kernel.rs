//! Native Lean kernel launcher and independent finite differential experiment.
//!
//! This example grants no `VerifiedProgram` or QIRF authority. The supplied
//! executable checks the experimental phase-word artifact and a separate request.
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use qleisli_core::contract::exact::{Budget, Exact, Matrix};
use qleisli_core::contract::{BasisType, Circuit};
use qleisli_core::ir::{CircuitAction, CircuitStep};

const HEADER: &str = "qleisli.phase-word 1 phase256-word-v1\nBit->Bit\n";
const OUTPUT_LIMIT: u64 = 65_536;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(Clone, Copy)]
enum Gate {
    X,
    Phase(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Summary {
    flip: bool,
    phase0: u8,
    phase1: u8,
}

impl Summary {
    const IDENTITY: Self = Self {
        flip: false,
        phase0: 0,
        phase1: 0,
    };
    fn text(self) -> String {
        format!("{} {} {}", u8::from(self.flip), self.phase0, self.phase1)
    }
}

/// Two independent basis trajectories; no Lean normalizer or returned summary.
fn oracle(word: &[Gate]) -> Summary {
    let mut outputs = [(false, 0u8), (true, 0u8)];
    for (bit, phase) in &mut outputs {
        for gate in word {
            match *gate {
                Gate::X => *bit = !*bit,
                Gate::Phase(ticks) if *bit => *phase = phase.wrapping_add(ticks),
                Gate::Phase(_) => {}
            }
        }
    }
    assert_ne!(outputs[0].0, outputs[1].0);
    Summary {
        flip: outputs[0].0,
        phase0: outputs[0].1,
        phase1: outputs[1].1,
    }
}

fn artifact(word: &[Gate], claim: Summary) -> String {
    let mut text = format!("{HEADER}claim {}\n{}\n", claim.text(), word.len());
    for gate in word {
        match gate {
            Gate::X => text.push_str("x\n"),
            Gate::Phase(ticks) => text.push_str(&format!("phase {ticks}\n")),
        }
    }
    text
}

fn requirement(summary: Summary) -> String {
    format!("{HEADER}expect {}\n", summary.text())
}

fn result_json(accepted: bool, code: &str, stage: &str) -> String {
    format!(
        "{{\"format\":\"qleisli.kernel-result\",\"version\":1,\"profile\":\"phase256-word-v1\",\"accepted\":{accepted},\"code\":\"{code}\",\"stage\":\"{stage}\"}}\n"
    )
}

/// Bound process time and both output streams. Missing/crashed/malformed kernels
/// are errors; this launcher never substitutes a Rust acceptance decision.
fn invoke(binary: &Path, program: &Path, required: &Path) -> Result<(i32, String)> {
    let mut child = Command::new(binary)
        .args([program, required])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let stdout = child.stdout.take().ok_or("missing stdout pipe")?;
    let stderr = child.stderr.take().ok_or("missing stderr pipe")?;
    let read = |pipe: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = vec![];
            pipe.take(OUTPUT_LIMIT + 1)
                .read_to_end(&mut bytes)
                .map(|_| bytes)
        })
    };
    let out = read(Box::new(stdout));
    let err = read(Box::new(stderr));
    let deadline = Instant::now() + Duration::from_secs(5);
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            // Close/drain the child's streams after termination.
            let _ = out.join();
            let _ = err.join();
            return Err("Lean kernel timed out; no fallback acceptance".into());
        }
        std::thread::sleep(Duration::from_millis(1));
    };
    let stdout = out.join().map_err(|_| "stdout reader failed")??;
    let stderr = err.join().map_err(|_| "stderr reader failed")??;
    if stdout.len() as u64 > OUTPUT_LIMIT || stderr.len() as u64 > OUTPUT_LIMIT {
        return Err("Lean kernel exceeded output limit".into());
    }
    if !stderr.is_empty() {
        return Err("Lean kernel emitted unexpected stderr".into());
    }
    let code = status
        .code()
        .ok_or("Lean kernel terminated without an exit code")?;
    let text = String::from_utf8(stdout)?;
    let accepted = code == 0 && text == result_json(true, "accepted", "verification");
    let rejected = code == 1
        && ["rejected", "syntax", "limit", "io"]
            .into_iter()
            .any(|reason| {
                ["artifact", "requirement", "verification"]
                    .into_iter()
                    .any(|stage| text == result_json(false, reason, stage))
            });
    if !accepted && !rejected {
        return Err("Lean kernel returned an invalid result or crashed".into());
    }
    Ok((code, text))
}

struct Temp(PathBuf);
impl Temp {
    fn new() -> Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        loop {
            let path = std::env::temp_dir().join(format!(
                "qleisli-lean-kernel-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }
    }
    fn check(
        &self,
        binary: &Path,
        input: &str,
        expected: &str,
        code: &str,
        stage: &str,
    ) -> Result<()> {
        let accepted = code == "accepted";
        let program = self.0.join("input.qpk");
        let required = self.0.join("request.qpr");
        fs::write(&program, input)?;
        fs::write(&required, expected)?;
        let result = invoke(binary, &program, &required)?;
        if result.0 != i32::from(!accepted) || result.1 != result_json(accepted, code, stage) {
            return Err(
                format!("expected {accepted}/{code}/{stage}, received {}", result.1).into(),
            );
        }
        Ok(())
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Existing Rust exact circuit evaluation is a second oracle on the zeta8 subset.
fn check_exact_matrix(word: &[Gate], expected: Summary) -> Result<()> {
    let steps = word
        .iter()
        .map(|gate| CircuitStep {
            controls: vec![],
            action: match gate {
                Gate::X => CircuitAction::Monomial {
                    indices: vec![0],
                    permutation: vec![1, 0],
                    phases: vec![0, 0],
                },
                Gate::Phase(ticks) => {
                    assert_eq!(ticks % 32, 0);
                    CircuitAction::Monomial {
                        indices: vec![0],
                        permutation: vec![0, 1],
                        phases: vec![0, ticks / 32],
                    }
                }
            },
        })
        .collect();
    let actual = Circuit::new(BasisType::Bit, steps)?.matrix(&mut Budget::new(100_000))?;
    let mut entries = vec![Exact::zero(); 4];
    for (column, phase) in [expected.phase0, expected.phase1].into_iter().enumerate() {
        let row = column ^ usize::from(expected.flip);
        entries[row * 2 + column] = Exact::phase(i32::from(phase / 32));
    }
    if actual != Matrix::new(2, 2, entries)? {
        return Err("independent matrix oracle disagrees".into());
    }
    Ok(())
}

fn self_test(binary: &Path) -> Result<()> {
    let temp = Temp::new()?;
    temp.check(
        binary,
        include_str!("../tests/fixtures/lean_kernel/phase_pair.qpk"),
        include_str!("../tests/fixtures/lean_kernel/t_expected.qpr"),
        "accepted",
        "verification",
    )?;
    temp.check(
        binary,
        include_str!("../tests/fixtures/lean_kernel/global_phase.qpk"),
        include_str!("../tests/fixtures/lean_kernel/identity.qpr"),
        "rejected",
        "verification",
    )?;
    let mut decisions = 2usize;
    let mut words = vec![vec![]];
    // All words of length 0..4 over X, I, T and T-adjoint (341 words).
    for length in 0..=4 {
        for word in &words {
            let expected = oracle(word);
            check_exact_matrix(word, expected)?;
            temp.check(
                binary,
                &artifact(word, expected),
                &requirement(expected),
                "accepted",
                "verification",
            )?;
            let wrong = Summary {
                phase0: expected.phase0.wrapping_add(32),
                ..expected
            };
            // A producer changing both its proof and desired claim cannot alter
            // the separately fixed request or the actual circuit's meaning.
            temp.check(
                binary,
                &artifact(word, wrong),
                &requirement(wrong),
                "rejected",
                "verification",
            )?;
            temp.check(
                binary,
                &artifact(word, expected),
                &requirement(wrong),
                "rejected",
                "verification",
            )?;
            decisions += 3;
        }
        if length < 4 {
            words = words
                .iter()
                .flat_map(|word| {
                    [Gate::X, Gate::Phase(0), Gate::Phase(32), Gate::Phase(224)].map(|gate| {
                        let mut next = word.clone();
                        next.push(gate);
                        next
                    })
                })
                .collect();
        }
    }
    for ticks in 0..=255 {
        let word = [Gate::Phase(ticks), Gate::X, Gate::Phase(ticks), Gate::X];
        let scalar = Summary {
            flip: false,
            phase0: ticks,
            phase1: ticks,
        };
        assert_eq!(oracle(&word), scalar);
        temp.check(
            binary,
            &artifact(&word, scalar),
            &requirement(scalar),
            "accepted",
            "verification",
        )?;
        decisions += 1;
    }
    let original = artifact(
        &[Gate::Phase(16), Gate::Phase(16)],
        Summary {
            flip: false,
            phase0: 0,
            phase1: 32,
        },
    );
    let expected = requirement(Summary {
        flip: false,
        phase0: 0,
        phase1: 32,
    });
    let changed = original.replacen("phase 16", "phase 17", 1);
    temp.check(binary, &changed, &expected, "rejected", "verification")?;
    let scalar = artifact(
        &[Gate::X, Gate::Phase(16), Gate::X, Gate::Phase(16)],
        Summary {
            flip: false,
            phase0: 16,
            phase1: 16,
        },
    );
    temp.check(
        binary,
        &scalar,
        &requirement(Summary::IDENTITY),
        "rejected",
        "verification",
    )?;
    decisions += 2;
    for bad in [
        original.replace("Bit->Bit", "Unit->Unit"),
        original.replace("phase 16", "phase 016"),
        original.replace("phase 16", "phase -0"),
        original.replace("phase 16", "phase 1e1"),
        original.replace("phase 16", "phase 16.0"),
        original.replace("phase 16", "h"),
        original.replace('\n', "\r\n"),
        format!("{original}\n"),
        original.trim_end().into(),
        original.replace("\n2\n", "\n0\n"),
        original.replace("phase256-word-v1", "unknown"),
        original.replace("word 1", "word 2"),
        format!("{original}\0"),
    ] {
        temp.check(binary, &bad, &expected, "syntax", "artifact")?;
        decisions += 1;
    }
    for bad in [
        original.replace("claim 0", "claim 2"),
        original.replace("phase 16", "phase 256"),
        artifact(&vec![Gate::X; 4097], Summary::IDENTITY),
    ] {
        temp.check(binary, &bad, &expected, "limit", "artifact")?;
        decisions += 1;
    }
    temp.check(
        binary,
        &original,
        &expected.replace("expect", "claim"),
        "syntax",
        "requirement",
    )?;
    temp.check(binary, &" ".repeat(65_537), &expected, "limit", "artifact")?;
    temp.check(
        binary,
        &original,
        &" ".repeat(65_537),
        "limit",
        "requirement",
    )?;
    decisions += 3;
    let max = vec![Gate::Phase(255); 4096];
    temp.check(
        binary,
        &artifact(&max, oracle(&max)),
        &requirement(oracle(&max)),
        "accepted",
        "verification",
    )?;
    decisions += 1;
    let program = temp.0.join("input.qpk");
    let required = temp.0.join("request.qpr");
    let missing = temp.0.join("missing");
    for (program, required, stage) in [
        (&missing, &required, "artifact"),
        (&program, &missing, "requirement"),
    ] {
        let result = invoke(binary, program, required)?;
        assert_eq!(result, (1, result_json(false, "io", stage)));
        decisions += 1;
    }
    fs::write(&program, [0xff])?;
    assert_eq!(
        invoke(binary, &program, &required)?,
        (1, result_json(false, "syntax", "artifact"))
    );
    decisions += 1;
    let usage = Command::new(binary).output()?;
    assert_eq!(usage.status.code(), Some(2));
    assert_eq!(
        usage.stdout,
        result_json(false, "usage", "usage").as_bytes()
    );
    assert!(usage.stderr.is_empty());
    decisions += 1;
    // Infrastructure failures cannot be converted into Rust acceptance.
    assert!(invoke(&missing, &program, &required).is_err());
    assert!(invoke(&std::env::current_exe()?, &program, &required).is_err());
    println!(
        "Passed {decisions} native Lean decisions; 341 Rust exact-matrix oracles; all 256 dyadic scalar phases."
    );
    Ok(())
}

fn run() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    match args.as_slice() {
        [binary, mode] if mode == "--self-test" => self_test(Path::new(binary)),
        [binary, artifact, requirement] => {
            let (code, output) = invoke(
                Path::new(binary),
                Path::new(artifact),
                Path::new(requirement),
            )?;
            print!("{output}");
            if code != 0 {
                return Err("Lean kernel rejected the artifact/request".into());
            }
            Ok(())
        }
        _ => Err(
            "usage: lean_kernel KERNEL ARTIFACT REQUIREMENT | lean_kernel KERNEL --self-test"
                .into(),
        ),
    }
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::FAILURE
        }
    }
}
