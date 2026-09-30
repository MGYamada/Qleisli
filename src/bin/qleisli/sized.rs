//! Bounded sized source through independent hierarchy checking and execution.
use qleisli::{
    frontend::sized::{OperationBinding, ParsedProgram, SourceType, SourceValue},
    interchange::hierarchical::{
        Kernel,
        execution::{ExecutionLimits, SamplingLimits},
    },
    sim::SplitMix64,
};
use std::{collections::BTreeMap, ffi::OsString, io::Read, path::PathBuf, process::ExitCode};

const USAGE: &str = "usage: qleisli sized <check|run|sample|emit-proposal> --entry=module::function
  --module=name=PATH (repeat) --nat=name=N (repeat)
  [--operation=name=module::function --operation-nat=name.parameter=N] (repeat)
  --kernel=PATH [--request=PATH | --qpe-provider=PATH]
  [--basis=N] [--shots=N --seed=N] [--output=PATH]
  run/sample start in the explicit input basis (default 0). sample requires shots and seed.
  emit-proposal requires output and no kernel; it emits untrusted JSON.
  check/run/sample independently check the emitted composition against a producer-derived request.
  --request adds a caller-supplied composition contract; --qpe-provider adds the named QPE contract.";

type Result<T> = std::result::Result<T, String>;
#[derive(Default)]
struct Options {
    command: String,
    entry: String,
    modules: BTreeMap<String, PathBuf>,
    ns: BTreeMap<String, u32>,
    ops: BTreeMap<String, String>,
    op_ns: BTreeMap<String, BTreeMap<String, u32>>,
    kernel: Option<PathBuf>,
    request: Option<PathBuf>,
    provider: Option<PathBuf>,
    output: Option<PathBuf>,
    basis: usize,
    shots: Option<usize>,
    seed: Option<u64>,
}
fn natural<T: std::str::FromStr>(s: &str) -> Option<T> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) || s.len() > 1 && s.starts_with('0') {
        None
    } else {
        s.parse().ok()
    }
}
fn options(args: &[OsString]) -> Option<Options> {
    let mut result = Options {
        command: args.first()?.to_str()?.into(),
        ..Options::default()
    };
    let mut singleton = std::collections::BTreeSet::new();
    for a in &args[1..] {
        let (flag, value) = a.to_str()?.strip_prefix("--")?.split_once('=')?;
        if value.is_empty() {
            return None;
        }
        if !matches!(flag, "module" | "nat" | "operation" | "operation-nat")
            && !singleton.insert(flag)
        {
            return None;
        }
        match flag {
            "entry" => result.entry = value.into(),
            "module" => {
                let (k, v) = value.split_once('=')?;
                if v.is_empty() || result.modules.insert(k.into(), v.into()).is_some() {
                    return None;
                }
            }
            "nat" => {
                let (k, v) = value.split_once('=')?;
                if result.ns.insert(k.into(), natural(v)?).is_some() {
                    return None;
                }
            }
            "operation" => {
                let (k, v) = value.split_once('=')?;
                if result.ops.insert(k.into(), v.into()).is_some() {
                    return None;
                }
            }
            "operation-nat" => {
                let (key, v) = value.split_once('=')?;
                let (op, k) = key.split_once('.')?;
                if result
                    .op_ns
                    .entry(op.into())
                    .or_default()
                    .insert(k.into(), natural(v)?)
                    .is_some()
                {
                    return None;
                }
            }
            "kernel" => result.kernel = Some(value.into()),
            "request" => result.request = Some(value.into()),
            "qpe-provider" => result.provider = Some(value.into()),
            "output" => result.output = Some(value.into()),
            "basis" => result.basis = natural(value)?,
            "shots" => result.shots = Some(natural(value)?),
            "seed" => result.seed = Some(natural(value)?),
            _ => return None,
        }
    }
    if result.entry.is_empty()
        || result.modules.is_empty()
        || result.request.is_some() && result.provider.is_some()
        || result.op_ns.keys().any(|k| !result.ops.contains_key(k))
    {
        return None;
    }
    match result.command.as_str() {
        "emit-proposal"
            if result.output.is_some()
                && result.kernel.is_none()
                && result.request.is_none()
                && result.provider.is_none()
                && result.shots.is_none()
                && result.seed.is_none()
                && !singleton.contains("basis") => {}
        "check" | "run"
            if result.kernel.is_some()
                && result.output.is_none()
                && result.shots.is_none()
                && result.seed.is_none() => {}
        "sample"
            if result.kernel.is_some()
                && result.output.is_none()
                && result.shots.is_some_and(|n| (1..=1024).contains(&n))
                && result.seed.is_some() => {}
        _ => return None,
    }
    Some(result)
}
fn read(path: &PathBuf) -> Result<Vec<u8>> {
    let mut bytes = vec![];
    std::fs::File::open(path)
        .map_err(|e| e.to_string())?
        .take((16 << 20) + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > 16 << 20 {
        return Err("request exceeds 16 MiB".into());
    }
    Ok(bytes)
}
fn width(ty: &SourceType) -> usize {
    if ty.is_quantum() {
        ty.width().unwrap_or(0) as usize
    } else {
        ty.fields().iter().map(width).sum()
    }
}
fn execute(mut o: Options) -> Result<String> {
    let contract = if o.provider.is_some() {
        "qpe"
    } else if o.request.is_some() {
        "requested-composition"
    } else {
        "composition"
    };
    let ops = o
        .ops
        .into_iter()
        .map(|(name, definition)| {
            let ns = o.op_ns.remove(&name).unwrap_or_default();
            (name, OperationBinding::new(definition, ns))
        })
        .collect();
    let source = ParsedProgram::load(o.modules)
        .map_err(|e| e.to_string())?
        .instantiate(&o.entry, o.ns, ops)
        .map_err(|e| e.to_string())?
        .elaborate()
        .map_err(|e| e.to_string())?;
    let root = &source.definitions()[source.root()];
    let bits = root
        .inputs()
        .iter()
        .map(SourceValue::ty)
        .map(width)
        .sum::<usize>();
    if bits > 16 || o.basis >= 1usize << bits {
        return Err("input basis is outside the entry's quantum type".into());
    }
    let proposal = source.lower().map_err(|e| e.to_string())?;
    if let Some(path) = o.output {
        std::fs::write(&path, proposal.payload()).map_err(|e| e.to_string())?;
        return Ok("{\"status\":\"untrusted-proposal\"}".into());
    }
    let kernel = Kernel::new(o.kernel.ok_or("missing kernel")?);
    let mut input = vec![[0.0, 0.0]; 1usize << bits];
    input[o.basis] = [1.0, 0.0];
    let limits = ExecutionLimits {
        max_amplitudes: 1 << 20,
        max_steps: 10_000_000,
    };
    if proposal.is_instrument() {
        let named;
        let generic;
        let checked = if let Some(path) = o.provider {
            let binding = proposal
                .qpe_binding(&read(&path)?)
                .map_err(|e| e.to_string())?;
            named = kernel
                .check_qpe_instrument(proposal.payload(), binding.request(), binding.candidate())
                .map_err(|e| e.to_string())?;
            named.instrument()
        } else {
            let request = match o.request {
                Some(path) => read(&path)?,
                None => proposal.comparison_request().to_vec(),
            };
            generic = kernel
                .check_instrument(proposal.payload(), &request)
                .map_err(|e| e.to_string())?;
            &generic
        };
        proposal
            .validate_initialization_moves(checked)
            .map_err(|e| e.to_string())?;
        if o.command == "check" {
            return Ok(format!(
                "{{\"status\":\"checked\",\"profile\":\"sized-instrument\",\"contract\":\"{contract}\"}}"
            ));
        }
        if o.command == "sample" {
            let output = checked
                .sample_normalized_shots(
                    &input,
                    1,
                    o.shots.unwrap(),
                    &mut SplitMix64::new(o.seed.unwrap()),
                    SamplingLimits {
                        max_shots: 1024,
                        execution: limits,
                    },
                )
                .map_err(|e| e.to_string())?;
            return Ok(format!(
                "{{\"measured_bits\":{},\"outcomes\":{:?}}}",
                output.measured_bits,
                output.shots.iter().map(|s| s.outcome).collect::<Vec<_>>()
            ));
        }
        let output = checked
            .execute(&input, 1, limits)
            .map_err(|e| e.to_string())?;
        Ok(format!(
            "{{\"measured_bits\":{},\"residual_bits\":{},\"branches\":{:?}}}",
            output.measured_bits, output.residual_quantum_bits, output.branches
        ))
    } else {
        if o.provider.is_some() || o.command == "sample" {
            return Err("named QPE and sampling require an observing entry".into());
        }
        let request = match o.request {
            Some(path) => read(&path)?,
            None => proposal.comparison_request().to_vec(),
        };
        let checked = kernel
            .check_against(proposal.payload(), &request)
            .map_err(|e| e.to_string())?;
        if o.command == "check" {
            return Ok(format!(
                "{{\"status\":\"checked\",\"profile\":\"sized-unitary\",\"contract\":\"{contract}\"}}"
            ));
        }
        let output = checked
            .execute(&input, 1, limits)
            .map_err(|e| e.to_string())?;
        Ok(format!(
            "{{\"quantum_bits\":{},\"amplitudes\":{:?}}}",
            output.quantum_bits, output.amplitudes
        ))
    }
}
pub(super) fn run(args: &[OsString]) -> ExitCode {
    let Some(o) = options(args) else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    match execute(o) {
        Ok(out) => {
            println!("{out}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
