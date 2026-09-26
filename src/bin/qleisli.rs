use std::path::Path;
use std::process::ExitCode;

use qleisli_core::frontend::compile::{check_project, compile_project};
use qleisli_core::sim::{SimulationLimits, run_closed};

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 2 || !matches!(args[0].to_str(), Some("check" | "run")) {
        eprintln!("usage: qleisli <check|run> <source-root>");
        return ExitCode::from(2);
    }
    let source_root = Path::new(&args[1]);
    if args[0] == "check" {
        return match check_project(source_root) {
            Ok(()) => {
                println!("checked source and verified IR: {}", source_root.display());
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("{error}");
                ExitCode::FAILURE
            }
        };
    }
    let program = match compile_project(source_root) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
    };
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
