use std::io::Write;
use std::process::ExitCode;

use qleisli::frontend::diagnostic::Diagnostic;

#[path = "qleisli/artifacts.rs"]
mod artifacts;
#[path = "qleisli/check_report.rs"]
mod check_report;
#[path = "qleisli/digest.rs"]
mod digest;
#[path = "qleisli/engineering.rs"]
mod engineering;
#[path = "qleisli/engineering_instrument.rs"]
mod engineering_instrument;
#[path = "qleisli/engineering_openqasm.rs"]
mod engineering_openqasm;
#[path = "qleisli/engineering_openqasm_gate.rs"]
mod engineering_openqasm_gate;
#[path = "qleisli/engineering_pure_tensor.rs"]
mod engineering_pure_tensor;
#[path = "qleisli/interop.rs"]
mod interop;
#[path = "qleisli/json.rs"]
mod json;
#[path = "qleisli/options.rs"]
mod options;
#[path = "qleisli/samples.rs"]
mod samples;
#[path = "qleisli/source_commands.rs"]
mod source_commands;
#[path = "qleisli/source_plan.rs"]
mod source_plan;
#[path = "qleisli/verification_trace.rs"]
mod verification_trace;

fn write_stdout(bytes: &[u8], description: &str) -> ExitCode {
    match std::io::stdout().lock().write_all(bytes) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("could not write {description}: {error}");
            ExitCode::FAILURE
        }
    }
}

fn report(root: &std::path::Path, error: Diagnostic) {
    if let Some(p) = error.primary {
        eprintln!(
            "{}:{}:{}: {}: {}",
            p.path.display(),
            p.line,
            p.column,
            error.code,
            error.message
        );
    } else {
        eprintln!("{}: {}: {}", root.display(), error.code, error.message);
    }
}

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let mut trace = verification_trace::Command::default();
    if std::env::var_os("QLEISLI_VERIFICATION_TRACE").is_some_and(|flag| flag == "1") {
        let (status, native) =
            qleisli::interchange::verification_trace::capture(|| run(&args, &mut trace));
        trace.write(status, native);
        return status;
    }
    run(&args, &mut trace)
}

fn run(args: &[std::ffi::OsString], trace: &mut verification_trace::Command) -> ExitCode {
    // Discovery is documentation only and precedes every source/native route.
    // Exact standalone requests cannot swallow execution or format flags.
    if args.len() == 1 && (args[0] == "--help" || args[0] == "help") {
        trace.route = "help";
        return write_stdout(format!("{}\n", options::USAGE).as_bytes(), "help");
    }
    if args.len() == 2 && args[0] == "help" && args[1] == "ecosystem" {
        trace.route = "help";
        return write_stdout(options::ECOSYSTEM_HELP.as_bytes(), "ecosystem introduction");
    }
    if args
        .iter()
        .find(|arg| !arg.as_encoded_bytes().starts_with(b"-"))
        .is_some_and(|arg| arg == "sized")
    {
        let message = "the sized command was removed; use qleisli <check|run|sample|emit-proposal> --entry=MODULE::FUNCTION --module=NAME=PATH instead; see qleisli help ecosystem for tool discovery";
        if args.iter().any(|arg| arg == "--format=json") {
            let diagnostic = json::diagnostic_json(
                std::path::Path::new("."),
                &Diagnostic {
                    counterexample: None,
                    boundary: None,
                    code: "usage",
                    message: message.into(),
                    primary: None,
                },
            );
            if write_stdout(
                json::envelope("sized", Some(&diagnostic), "null").as_bytes(),
                "usage diagnostic",
            ) != ExitCode::SUCCESS
            {
                return ExitCode::FAILURE;
            }
        } else {
            eprintln!("usage: {message}");
        }
        return ExitCode::from(2);
    }
    if args.first().is_some_and(|arg| arg == "interop") {
        trace.route = "interop";
        return interop::run(&args[1..]);
    }
    if args.first().is_some_and(|arg| arg == "engineering") {
        trace.route = "engineering";
        return engineering::run(&args[1..]);
    }
    if source_plan::selected(args) {
        trace.route = "selected-source";
        return source_plan::run(args);
    }
    let json = args.iter().any(|arg| arg == "--format=json");
    let outcome = source_commands::dispatch(args, json);
    trace.source(&outcome);
    if json {
        return json::render(outcome);
    }
    render_text(outcome)
}

fn render_text(outcome: source_commands::Outcome) -> ExitCode {
    let source_root = &outcome.root;
    for warning in outcome.warnings {
        eprintln!("warning: {}", warning.message);
    }
    match outcome.result {
        Ok(source_commands::Success::Artifact(artifacts::Success::Emitted(path, report))) => {
            write_stdout(report.text(Some(&path)).as_bytes(), "emission result")
        }
        Ok(source_commands::Success::Artifact(artifacts::Success::Checked(report))) => {
            write_stdout(report.text(None).as_bytes(), "verification result")
        }
        Ok(source_commands::Success::Documentation(markdown)) => {
            write_stdout(markdown.as_bytes(), "documentation")
        }
        Err(source_commands::Failure::Artifact(error)) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
        Ok(source_commands::Success::Checked(checks)) => write_stdout(
            check_report::project_text(source_root, &checks).as_bytes(),
            "check result",
        ),
        Err(source_commands::Failure::Source(error)) => {
            if error.code == "usage" {
                eprintln!("{}", error.message);
                return ExitCode::from(2);
            }
            if error.code == "doc" {
                eprintln!("{}: {}", source_root.display(), error.message);
            } else {
                report(source_root, error);
            }
            ExitCode::FAILURE
        }
        Ok(source_commands::Success::Samples { shots, .. }) => {
            let mut text = String::new();
            for sample in shots {
                if sample.bits.is_empty() {
                    text.push_str("()");
                }
                for bit in sample.bits {
                    text.push(if bit { '1' } else { '0' });
                }
                text.push('\n');
            }
            write_stdout(text.as_bytes(), "sample results")
        }
        Ok(source_commands::Success::Distribution {
            probabilities,
            exact_zeros,
        }) => {
            use std::fmt::Write as _;
            let exact_zeros = match exact_zeros {
                Some(Ok(zeros)) => Some(zeros),
                Some(Err(reason)) => {
                    eprintln!(
                        "{}: exact-zero classification unavailable: {reason}",
                        source_root.display()
                    );
                    None
                }
                None => None,
            };
            let mut text = String::new();
            for (outcome, probability) in probabilities {
                let label: String = outcome
                    .iter()
                    .map(|bit| if *bit { '1' } else { '0' })
                    .collect();
                let annotation = if exact_zeros
                    .as_ref()
                    .is_some_and(|zeros| zeros.contains(&outcome))
                {
                    " [exact zero]"
                } else {
                    ""
                };
                writeln!(
                    text,
                    "{}: {probability:.12e}{annotation}",
                    if label.is_empty() { "()" } else { &label }
                )
                .expect("writing to String");
            }
            write_stdout(text.as_bytes(), "distribution")
        }
        Err(source_commands::Failure::Simulation(error)) => {
            eprintln!("{}", error.message);
            ExitCode::FAILURE
        }
    }
}
