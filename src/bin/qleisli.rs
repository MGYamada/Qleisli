use std::io::Write;
use std::process::ExitCode;

use qleisli_core::frontend::compile::{check_project_with_policy, compile_project_with_policy};
use qleisli_core::frontend::diagnostic::Diagnostic;
use qleisli_core::frontend::documentation::render_markdown;
use qleisli_core::frontend::project::read_source_file;
use qleisli_core::sim::{SimulationLimits, run_closed};

#[path = "qleisli/artifacts.rs"]
mod artifacts;
#[path = "qleisli/json.rs"]
mod json;
#[path = "qleisli/options.rs"]
mod options;
#[path = "qleisli/samples.rs"]
mod samples;

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
    if args.iter().any(|arg| arg == "--format=json") {
        return json::run(&args);
    }
    let Some(options) = options::Options::parse(&args, false) else {
        eprintln!("usage: qleisli <check|run> <source-root>\n       qleisli doc <source-file>");
        return ExitCode::from(2);
    };
    let source_root = &options.path;
    if matches!(options.command.as_str(), "emit-ir" | "verify-ir") {
        return match artifacts::execute(&options) {
            Ok(artifacts::Success::Emitted(path)) => {
                println!("emitted independently verified IR: {path}");
                ExitCode::SUCCESS
            }
            Ok(artifacts::Success::Verified(request)) => {
                println!("verified IR; request_checked: {request}");
                ExitCode::SUCCESS
            }
            Err(artifacts::Failure::Source(error)) => {
                report(source_root, error);
                ExitCode::FAILURE
            }
            Err(artifacts::Failure::Artifact(error)) => {
                eprintln!("{error}");
                ExitCode::FAILURE
            }
        };
    }
    if options.command == "doc" {
        let source = match read_source_file(source_root, options.policy) {
            Ok(source) => source,
            Err(error) => {
                report(source_root, error);
                return ExitCode::FAILURE;
            }
        };
        return match render_markdown(&source) {
            Ok(markdown) => match std::io::stdout().lock().write_all(markdown.as_bytes()) {
                Ok(()) => ExitCode::SUCCESS,
                Err(error) => {
                    eprintln!("could not write documentation: {error}");
                    ExitCode::FAILURE
                }
            },
            Err(error) => {
                eprintln!("{}: {error}", source_root.display());
                ExitCode::FAILURE
            }
        };
    }
    if options.command == "check" {
        return match check_project_with_policy(source_root, options.policy) {
            Ok(()) => {
                println!("checked source and verified IR: {}", source_root.display());
                ExitCode::SUCCESS
            }
            Err(error) => {
                report(source_root, error);
                ExitCode::FAILURE
            }
        };
    }
    let program = match compile_project_with_policy(source_root, options.policy) {
        Ok(program) => program,
        Err(error) => {
            report(source_root, error);
            return ExitCode::FAILURE;
        }
    };
    if options.command == "sample" {
        return match samples::collect(&program, options.shots.unwrap(), options.seed.unwrap()) {
            Ok((samples, _)) => {
                let mut text = String::new();
                for sample in samples {
                    if sample.bits.is_empty() {
                        text.push_str("()");
                    }
                    for bit in sample.bits {
                        text.push(if bit { '1' } else { '0' });
                    }
                    text.push('\n');
                }
                match std::io::stdout().lock().write_all(text.as_bytes()) {
                    Ok(()) => ExitCode::SUCCESS,
                    Err(e) => {
                        eprintln!("could not write sample results: {e}");
                        ExitCode::FAILURE
                    }
                }
            }
            Err(error) => {
                report(source_root, error);
                ExitCode::FAILURE
            }
        };
    }
    match run_closed(&program, SimulationLimits::default()) {
        Ok(distribution) => {
            for (outcome, probability) in distribution {
                let label: String = outcome
                    .iter()
                    .map(|bit| if *bit { '1' } else { '0' })
                    .collect();
                println!(
                    "{}: {probability:.12e}",
                    if label.is_empty() { "()" } else { &label }
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
