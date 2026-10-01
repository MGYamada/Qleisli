//! Bounded sized source through independent hierarchy checking and execution.
use qleisli::{
    frontend::sized::{OperationBinding, ParsedProgram, SourceType, SourceValue},
    interchange::hierarchical::{
        Kernel,
        execution::{ExecutionLimits, SamplingLimits},
    },
    sim::SplitMix64,
};
use std::{ffi::OsString, io::Read, path::PathBuf, process::ExitCode};

#[path = "sized/options.rs"]
mod options;
use options::{Options, USAGE};

type Result<T> = std::result::Result<T, String>;
#[derive(Clone, Copy)]
enum RequestScope {
    ProducerConsistency,
    CallerComposition,
    NamedQpe,
}
impl RequestScope {
    fn name(self) -> &'static str {
        match self {
            Self::ProducerConsistency => "producer-consistency",
            Self::CallerComposition => "caller-composition",
            Self::NamedQpe => "named-qpe",
        }
    }
    fn contract(self) -> &'static str {
        match self {
            Self::ProducerConsistency => "composition",
            Self::CallerComposition => "requested-composition",
            Self::NamedQpe => "qpe",
        }
    }
    fn report(self) -> String {
        let (scope, origin, authority) = match self {
            Self::ProducerConsistency => {
                ("producer-consistency", "producer", "checked-produced-ir")
            }
            Self::CallerComposition => (
                "caller-composition",
                "caller",
                "checked-ir-against-caller-request",
            ),
            Self::NamedQpe => (
                "named-qpe",
                "caller-provider",
                "checked-ir-against-named-qpe",
            ),
        };
        format!(
            "\"verification\":{{\"scope\":\"{scope}\",\"request_origin\":\"{origin}\",\"source_meaning_verified\":false}},\"execution_authority\":\"{authority}\""
        )
    }
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
    let scope = if o.provider.is_some() {
        RequestScope::NamedQpe
    } else if o.request.is_some() {
        RequestScope::CallerComposition
    } else {
        RequestScope::ProducerConsistency
    };
    let contract = scope.contract();
    let verification = scope.report();
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
    let input = if matches!(o.command.as_str(), "run" | "sample") {
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
        let mut input = vec![[0.0, 0.0]; 1usize << bits];
        input[o.basis] = [1.0, 0.0];
        Some(input)
    } else {
        None
    };
    let proposal = source.lower().map_err(|e| e.to_string())?;
    let checking_error = |e: qleisli::interchange::Error| {
        format!(
            "{e}; sized {} profile, {} contract",
            if proposal.is_instrument() {
                "instrument"
            } else {
                "unitary"
            },
            scope.name()
        )
    };
    if let Some(path) = o.output {
        std::fs::write(&path, proposal.payload()).map_err(|e| e.to_string())?;
        return Ok("{\"status\":\"untrusted-proposal\"}".into());
    }
    let kernel = Kernel::new(o.kernel.ok_or("missing kernel")?);
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
                .map_err(checking_error)?;
            named.instrument()
        } else {
            let request = match o.request {
                Some(path) => read(&path)?,
                None => proposal.comparison_request().to_vec(),
            };
            generic = kernel
                .check_instrument(proposal.payload(), &request)
                .map_err(checking_error)?;
            &generic
        };
        proposal
            .validate_initialization_moves(checked)
            .map_err(|e| e.to_string())?;
        if o.command == "check" {
            return Ok(format!(
                "{{\"status\":\"checked\",\"profile\":\"sized-instrument\",\"contract\":\"{contract}\",{verification}}}"
            ));
        }
        let input = input.as_deref().ok_or("missing execution input")?;
        if o.command == "sample" {
            let output = checked
                .sample_normalized_shots(
                    input,
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
                "{{\"measured_bits\":{},\"outcomes\":{:?},{verification}}}",
                output.measured_bits,
                output.shots.iter().map(|s| s.outcome).collect::<Vec<_>>()
            ));
        }
        let output = checked
            .execute(input, 1, limits)
            .map_err(|e| e.to_string())?;
        Ok(format!(
            "{{\"measured_bits\":{},\"residual_bits\":{},\"branches\":{:?},{verification}}}",
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
            .map_err(checking_error)?;
        if o.command == "check" {
            return Ok(format!(
                "{{\"status\":\"checked\",\"profile\":\"sized-unitary\",\"contract\":\"{contract}\",{verification}}}"
            ));
        }
        let input = input.as_deref().ok_or("missing execution input")?;
        let output = checked
            .execute(input, 1, limits)
            .map_err(|e| e.to_string())?;
        Ok(format!(
            "{{\"quantum_bits\":{},\"amplitudes\":{:?},{verification}}}",
            output.quantum_bits, output.amplitudes
        ))
    }
}
pub(super) fn run(args: &[OsString]) -> ExitCode {
    let Some(o) = options::parse(args) else {
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
