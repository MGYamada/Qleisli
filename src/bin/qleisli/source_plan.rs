//! Source specialization, proposal preparation, and native-checked execution.
//! A plan/proposal carries no native acceptance authority.

use qleisli::{
    frontend::{
        ast::Span,
        compile::{
            self, BasisBinding, ElaboratedProgram, HierarchyEligibility, HierarchyProposal,
            OperationBinding, ParsedProgram, QpeBindingProposal, RawSourceProposal, SourceType,
        },
        diagnostic::Diagnostic,
    },
    interchange::{self, hierarchical, native},
    sim::{SimulationLimits, SplitMix64, run_closed},
};
use std::{
    ffi::OsString,
    io::Read,
    path::{Path, PathBuf},
    process::ExitCode,
};

#[path = "source_plan/options.rs"]
mod options;
use super::json::quoted;
use options::{IrProfile, Options};

type Result<T> = std::result::Result<T, Failure>;

struct SourceSite {
    module: String,
    span: Span,
}
struct Failure {
    code: String,
    message: String,
    text: String,
    site: Option<Box<SourceSite>>,
    pointer: Option<String>,
}
impl Failure {
    fn new(code: &str, message: impl Into<String>) -> Self {
        let message = message.into();
        Self {
            code: code.into(),
            text: message.clone(),
            message,
            site: None,
            pointer: None,
        }
    }
    fn at_root(source: &ElaboratedProgram, message: &str) -> Self {
        let root = &source.definitions()[source.root()];
        let mut failure = Self::new("unsupported", message);
        failure.site = Some(Box::new(SourceSite {
            module: root
                .path()
                .rsplit_once("::")
                .map_or(root.path(), |(module, _)| module)
                .into(),
            span: root.span(),
        }));
        failure
    }
    fn hierarchy(error: interchange::Error, profile: &str, scope: RequestScope) -> Self {
        let mut failure = Self::from(error);
        failure.text = format!(
            "{}; sized {} profile, {} contract",
            failure.text,
            profile,
            scope.name()
        );
        failure.message = failure.text.clone();
        failure
    }
    fn diagnostic(&self, options: Option<&Options>) -> String {
        let primary = self.site.as_ref().map(|site| {
            let path = options
                .and_then(|o| o.modules.get(&site.module))
                .and_then(|p| p.to_str());
            // The loader reports original byte spans but not original line/column
            // coordinates on failure. Never reread files or invent coordinates.
            format!(
                "{{\"module\":{},\"path\":{},\"start\":{},\"end\":{}}}",
                quoted(&site.module),
                path.map(quoted).unwrap_or_else(|| "null".into()),
                site.span.start,
                site.span.end
            )
        });
        let related = self.pointer.as_ref().map(|pointer| {
            format!(
                "{{\"message\":{},\"location\":null}}",
                quoted(&format!("json_pointer: {pointer}"))
            )
        });
        format!(
            "{{\"code\":{},\"severity\":\"error\",\"message\":{},\"primary\":{},\"related\":[{}]}}",
            quoted(&self.code),
            quoted(&self.message),
            primary.as_deref().unwrap_or("null"),
            related.as_deref().unwrap_or("")
        )
    }
}
impl From<compile::Error> for Failure {
    fn from(error: compile::Error) -> Self {
        Self {
            code: error.code().into(),
            message: error.message().into(),
            text: error.to_string(),
            site: error.module().map(|module| {
                Box::new(SourceSite {
                    module: module.into(),
                    span: error.span(),
                })
            }),
            pointer: None,
        }
    }
}
impl From<interchange::Error> for Failure {
    fn from(error: interchange::Error) -> Self {
        let text = error.to_string();
        Self {
            code: error.code.into(),
            message: error.message,
            text,
            site: None,
            pointer: (!error.json_pointer.is_empty()).then_some(error.json_pointer),
        }
    }
}
impl From<Diagnostic> for Failure {
    fn from(error: Diagnostic) -> Self {
        Self::new(error.code, error.message)
    }
}
impl<E: std::fmt::Display> From<hierarchical::execution::SamplingError<E>> for Failure {
    fn from(error: hierarchical::execution::SamplingError<E>) -> Self {
        use hierarchical::execution::SamplingError;
        match error {
            SamplingError::Execution(error) => Self::from(error),
            SamplingError::RandomSource(error) => {
                Self::new("random_source", format!("random source failed: {error}"))
            }
            SamplingError::Numerical(reason) => {
                Self::new("numerical", format!("numerical sampling failure: {reason}"))
            }
        }
    }
}

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
        let (origin, authority) = match self {
            Self::ProducerConsistency => ("producer", "checked-produced-ir"),
            Self::CallerComposition => ("caller", "checked-ir-against-caller-request"),
            Self::NamedQpe => ("caller-provider", "checked-ir-against-named-qpe"),
        };
        format!(
            "\"verification\":{{\"scope\":\"{}\",\"request_origin\":\"{origin}\",\"source_meaning_verified\":false}},\"execution_authority\":\"{authority}\"",
            self.name()
        )
    }
}

enum PreparedRequest {
    Composition { bytes: Vec<u8>, scope: RequestScope },
    NamedQpe(QpeBindingProposal),
}
impl PreparedRequest {
    fn scope(&self) -> RequestScope {
        match self {
            Self::Composition { scope, .. } => *scope,
            Self::NamedQpe(_) => RequestScope::NamedQpe,
        }
    }
}
enum PreparedIr {
    Raw(Box<RawSourceProposal>),
    Hierarchy {
        proposal: Box<HierarchyProposal>,
        request: PreparedRequest,
        input: Option<Vec<[f64; 2]>>,
    },
}
impl PreparedIr {
    fn name(&self) -> &'static str {
        match self {
            Self::Raw(_) => "raw",
            Self::Hierarchy { .. } => "hierarchy",
        }
    }
    fn payload(&self) -> &[u8] {
        match self {
            Self::Raw(p) => p.payload(),
            Self::Hierarchy { proposal, .. } => proposal.payload(),
        }
    }
}

fn read(path: &Path) -> Result<Vec<u8>> {
    let mut bytes = vec![];
    std::fs::File::open(path)
        .map_err(|e| Failure::new("io", e.to_string()))?
        .take((16 << 20) + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| Failure::new("io", e.to_string()))?;
    if bytes.len() > 16 << 20 {
        return Err(Failure::new("limit", "request exceeds 16 MiB"));
    }
    Ok(bytes)
}
fn quantum(ty: &SourceType) -> bool {
    ty.is_quantum() || ty.fields().iter().any(quantum)
}
fn width(ty: &SourceType) -> usize {
    if ty.is_quantum() {
        ty.width().unwrap_or(0) as usize
    } else {
        ty.fields().iter().map(width).sum()
    }
}
fn prepare(options: &Options) -> Result<PreparedIr> {
    let program = ParsedProgram::load(options.modules.clone())?;
    fn bindings(
        values: &std::collections::BTreeMap<String, String>,
    ) -> Result<std::collections::BTreeMap<String, BasisBinding>> {
        values
            .iter()
            .map(|(name, source)| {
                BasisBinding::parse(source)
                    .map(|basis| (name.clone(), basis))
                    .map_err(|e| {
                        Failure::new(e.code(), format!("Basis binding {name}: {}", e.message()))
                    })
            })
            .collect()
    }
    let operations = options
        .ops
        .iter()
        .map(|(name, definition)| {
            Ok((
                name.clone(),
                OperationBinding::with_types(
                    definition.clone(),
                    bindings(&options.op_types.get(name).cloned().unwrap_or_default())?,
                    options.op_ns.get(name).cloned().unwrap_or_default(),
                ),
            ))
        })
        .collect::<Result<_>>()?;
    let source = program
        .instantiate_with_types(
            &options.entry,
            bindings(&options.types)?,
            options.ns.clone(),
            operations,
        )?
        .elaborate()?;
    let hierarchy = if options.request.is_some() || options.provider.is_some() {
        // Parsing rejects explicit Raw conflicts. Caller intent is never weakened
        // into a request-free native validity check.
        true
    } else {
        match options.ir_profile {
            IrProfile::Hierarchy => true,
            IrProfile::Raw => false,
            IrProfile::Auto => match source.hierarchy_eligibility()? {
                HierarchyEligibility::Eligible => true,
                HierarchyEligibility::Ineligible(_) => false,
            },
        }
    };
    let executing = matches!(options.command.as_str(), "run" | "sample");
    if !hierarchy {
        if options.basis.is_some() {
            return Err(Failure::at_root(
                &source,
                "--basis is unsupported for Raw execution; it is quantum hierarchy input, not ordinary data",
            ));
        }
        let root = &source.definitions()[source.root()];
        if executing && !root.inputs().is_empty() {
            return Err(Failure::at_root(
                &source,
                "Raw run/sample require zero runtime parameters; even a Unit parameter requires an explicit checked invocation",
            ));
        }
        if executing && quantum(root.output().ty()) {
            return Err(Failure::at_root(
                &source,
                "Raw run/sample require no quantum result",
            ));
        }
        // Full Raw capability checking is mandatory. A failure is final.
        return Ok(PreparedIr::Raw(Box::new(source.lower_raw()?)));
    }
    let input = if executing {
        let bits = source.definitions()[source.root()]
            .inputs()
            .iter()
            .map(|v| width(v.ty()))
            .sum::<usize>();
        let basis = options.basis.unwrap_or(0);
        if bits > 16 || basis >= 1usize << bits {
            return Err(Failure::at_root(
                &source,
                "input basis is outside the entry's quantum type",
            ));
        }
        let mut input = vec![[0.0, 0.0]; 1usize << bits];
        input[basis] = [1.0, 0.0];
        Some(input)
    } else {
        None
    };
    // Selection is already fixed. Neither lowering nor checking can reroute it.
    let root = &source.definitions()[source.root()];
    if root.effect() != "observe" && (options.provider.is_some() || options.command == "sample") {
        return Err(Failure::new(
            "unsupported",
            "named QPE and sampling require an observing entry",
        ));
    }
    let proposal = if source.has_operation_meanings() {
        source
            .check_operation_meanings(
                &native::Kernel::new(kernel_path(options)?),
                &mut qleisli::contract::exact::Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
            )?
            .lower_hierarchy()?
    } else {
        source.lower()?
    };
    let request = if let Some(path) = &options.provider {
        PreparedRequest::NamedQpe(proposal.qpe_binding(&read(path)?)?)
    } else {
        let (bytes, scope) = match &options.request {
            Some(path) => (read(path)?, RequestScope::CallerComposition),
            None => (
                proposal.comparison_request().to_vec(),
                RequestScope::ProducerConsistency,
            ),
        };
        PreparedRequest::Composition { bytes, scope }
    };
    Ok(PreparedIr::Hierarchy {
        proposal: Box::new(proposal),
        request,
        input,
    })
}

fn kernel_path(options: &Options) -> Result<PathBuf> {
    options
        .kernel
        .clone()
        .or_else(|| {
            std::env::var_os("QLEISLI_KERNEL")
                .filter(|p| !p.is_empty())
                .map(PathBuf::from)
        })
        .ok_or_else(|| {
            Failure::new(
                "kernel",
                "select the matching Lean checker with --lean-kernel=PATH or QLEISLI_KERNEL",
            )
        })
}
fn raw_execute(options: &Options, proposal: &RawSourceProposal, kernel: PathBuf) -> Result<String> {
    let checked = native::Kernel::new(kernel).accept(proposal.proposal())?;
    proposal.validate_source_steps(&checked)?;
    let result = match options.command.as_str() {
        "check" => "{\"status\":\"checked\"}".into(),
        "sample" => {
            let seed = options.seed.expect("parsed sample seed");
            let (shots, steps) = super::samples::collect(
                &checked,
                options.shots.expect("parsed sample shots") as u64,
                seed,
            )?;
            super::json::samples_json(&shots, seed, steps, ",")
        }
        _ => super::json::distribution_json(
            run_closed(&checked, SimulationLimits::default())
                .map_err(super::json::simulation_failure)?,
        )?,
    };
    Ok(fields(
        result,
        "\"verification\":{\"scope\":\"native-validity\",\"request_origin\":\"none\",\"source_steps_checked\":true,\"source_meaning_verified\":false},\"execution_authority\":\"checked-produced-ir\"",
    ))
}

fn hierarchy_execute(
    options: &Options,
    proposal: &HierarchyProposal,
    request: &PreparedRequest,
    input: Option<&[[f64; 2]]>,
    kernel: PathBuf,
) -> Result<String> {
    use hierarchical::execution::{ExecutionLimits, SamplingLimits};
    let scope = request.scope();
    let contract = scope.contract();
    let verification = scope.report();
    let isometry = proposal.source().definitions()[proposal.source().root()].effect() == "iso";
    let kernel = hierarchical::Kernel::new(kernel);
    let limits = ExecutionLimits {
        max_amplitudes: 1 << 20,
        max_steps: 10_000_000,
    };
    let profile = if isometry {
        "isometry"
    } else if proposal.is_instrument() {
        "instrument"
    } else {
        "unitary"
    };
    let checking_error = |error| Failure::hierarchy(error, profile, scope);
    if proposal.is_instrument() {
        let checked = match request {
            PreparedRequest::NamedQpe(binding) => kernel.check_qpe_instrument_native(
                proposal.payload(),
                binding.request(),
                binding.candidate(),
            ),
            PreparedRequest::Composition { bytes, .. } => {
                kernel.check_instrument_native(proposal.payload(), bytes)
            }
        }
        .map_err(checking_error)?;
        proposal.validate_initialization_moves_native(&checked)?;
        if options.command == "check" {
            let profile = if isometry {
                "sized-isometry"
            } else {
                "sized-instrument"
            };
            return Ok(format!(
                "{{\"status\":\"checked\",\"profile\":\"{profile}\",\"contract\":\"{contract}\",{verification}}}"
            ));
        }
        let input = input.expect("prepared execution input");
        if options.command == "sample" {
            let output = checked.sample_normalized_shots(
                input,
                1,
                options.shots.expect("parsed sample shots"),
                &mut SplitMix64::new(options.seed.expect("parsed sample seed")),
                SamplingLimits {
                    max_shots: 1024,
                    execution: limits,
                },
            )?;
            return Ok(format!(
                "{{\"measured_bits\":{},\"outcomes\":{:?},{verification}}}",
                output.measured_bits,
                output.shots.iter().map(|s| s.outcome).collect::<Vec<_>>()
            ));
        }
        let output = checked.execute_instrument(input, 1, limits)?;
        if isometry {
            if output.measured_bits != 0 || output.branches.len() != 1 {
                return Err(Failure::new(
                    "execution",
                    "empty-readout execution has an incompatible result shape",
                ));
            }
            // Preserve the actual unnormalized coefficient vector, including
            // its scalar phase. Shape checking is not an isometry proof.
            return Ok(format!(
                "{{\"quantum_bits\":{},\"amplitudes\":{:?},{verification}}}",
                output.residual_quantum_bits, output.branches[0]
            ));
        }
        Ok(format!(
            "{{\"measured_bits\":{},\"residual_bits\":{},\"branches\":{:?},{verification}}}",
            output.measured_bits, output.residual_quantum_bits, output.branches
        ))
    } else {
        let PreparedRequest::Composition { bytes, .. } = request else {
            unreachable!("named QPE requires an observing entry during preparation")
        };
        let checked = kernel
            .check_against_native(proposal.payload(), bytes)
            .map_err(checking_error)?;
        if options.command == "check" {
            return Ok(format!(
                "{{\"status\":\"checked\",\"profile\":\"sized-unitary\",\"contract\":\"{contract}\",{verification}}}"
            ));
        }
        let output = checked.execute_pure(input.expect("prepared execution input"), 1, limits)?;
        Ok(format!(
            "{{\"quantum_bits\":{},\"amplitudes\":{:?},{verification}}}",
            output.quantum_bits, output.amplitudes
        ))
    }
}

/// Extend a JSON object emitted by one of our own result constructors.
fn fields(mut object: String, extra: &str) -> String {
    debug_assert!(object.ends_with('}'));
    object.pop();
    object.push(',');
    object.push_str(extra);
    object.push('}');
    object
}
fn execute(options: &Options) -> Result<String> {
    let prepared = prepare(options)?;
    let emitted = options.command == "emit-proposal";
    let result = if emitted {
        super::artifacts::write_new(
            options.output.as_ref().expect("parsed output"),
            prepared.payload(),
        )
        .map_err(|error| match error {
            super::artifacts::Failure::Source(error) => Failure::from(error),
            super::artifacts::Failure::Artifact(error) => Failure::from(error),
        })?;
        "{\"status\":\"untrusted-proposal\"}".into()
    } else {
        let kernel = kernel_path(options)?;
        match &prepared {
            PreparedIr::Raw(proposal) => raw_execute(options, proposal, kernel)?,
            PreparedIr::Hierarchy {
                proposal,
                request,
                input,
            } => hierarchy_execute(options, proposal, request, input.as_deref(), kernel)?,
        }
    };
    Ok(fields(
        result,
        &format!(
            "\"entry\":{},\"ir_profile\":{},\"source_check_scope\":\"all-supplied-module-declarations\",\"native_check_scope\":{}",
            quoted(&options.entry),
            quoted(prepared.name()),
            quoted(if emitted {
                "none"
            } else {
                "selected-specialization"
            })
        ),
    ))
}

pub(super) fn selected(args: &[OsString]) -> bool {
    options::selected(args)
}

pub(super) fn run(args: &[OsString]) -> ExitCode {
    let options = options::parse(args);
    let command = args
        .iter()
        .find(|arg| !arg.as_encoded_bytes().starts_with(b"-"))
        .and_then(|arg| arg.to_str())
        .unwrap_or("");
    let json = args.iter().any(|arg| arg == "--format=json");
    let result = match &options {
        Some(options) => execute(options),
        None => Err(Failure::new("usage", options::USAGE)),
    };
    match result {
        Ok(result) => {
            let document = if json {
                super::json::envelope(command, None, &result)
            } else {
                format!("{result}\n")
            };
            super::write_stdout(document.as_bytes(), "selected source result")
        }
        Err(error) => {
            let status = ExitCode::from(if error.code == "usage" { 2 } else { 1 });
            if json {
                let document = super::json::envelope(
                    command,
                    Some(&error.diagnostic(options.as_ref())),
                    "null",
                );
                if super::write_stdout(document.as_bytes(), "selected source diagnostic")
                    != ExitCode::SUCCESS
                {
                    return ExitCode::FAILURE;
                }
            } else {
                eprintln!("{}", error.text);
            }
            status
        }
    }
}
