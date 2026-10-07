use std::io::Write;
use std::process::ExitCode;

use qleisli::frontend::diagnostic::Diagnostic;
use qleisli::frontend::documentation::render_markdown;
use qleisli::frontend::project::read_source_file;

#[path = "qleisli/artifacts.rs"]
mod artifacts;
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
    // Discovery is documentation only and precedes every source/native route.
    // Exact standalone requests cannot swallow execution or format flags.
    if args.len() == 1 && (args[0] == "--help" || args[0] == "help") {
        return write_stdout(format!("{}\n", options::USAGE).as_bytes(), "help");
    }
    if args.len() == 2 && args[0] == "help" && args[1] == "ecosystem" {
        return write_stdout(
            include_str!("../../docs/src/reference/discovery.md").as_bytes(),
            "ecosystem introduction",
        );
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
        return interop::run(&args[1..]);
    }
    if source_plan::selected(&args) {
        return source_plan::run(&args);
    }
    if args.iter().any(|arg| arg == "--format=json") {
        return json::run(&args);
    }
    let Some(mut options) = options::Options::parse(&args, false) else {
        eprintln!("{}", options::USAGE);
        return ExitCode::from(2);
    };
    if options.qrate {
        match qleisli::frontend::project::QrateSource::select(&options.path) {
            Ok(root) => {
                options.path = root.path().to_owned();
                options.selected_root = Some(root);
            }
            Err(error) => {
                report(&options.path, error);
                return ExitCode::FAILURE;
            }
        }
    }
    let source_root = &options.path;
    if options.command != "verify-ir" && options.command != "doc" {
        for warning in
            qleisli::frontend::project::manifest_warnings(source_root).unwrap_or_default()
        {
            eprintln!("warning: {}", warning.message);
        }
    }
    if matches!(options.command.as_str(), "emit-ir" | "verify-ir") {
        return match artifacts::execute(&options) {
            Ok(artifacts::Success::Emitted(path)) => write_stdout(
                format!("emitted independently verified IR: {path}\n").as_bytes(),
                "emission result",
            ),
            Ok(artifacts::Success::Verified(request)) => write_stdout(
                format!("verified IR; request_checked: {request}\n").as_bytes(),
                "verification result",
            ),
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
            Ok(markdown) => write_stdout(markdown.as_bytes(), "documentation"),
            Err(error) => {
                eprintln!("{}: {error}", source_root.display());
                ExitCode::FAILURE
            }
        };
    }
    match source_commands::execute(&options, source_root) {
        Ok(source_commands::Success::Checked) => write_stdout(
            format!(
                "checked source and verified IR: {}\n",
                source_root.display()
            )
            .as_bytes(),
            "check result",
        ),
        Err(source_commands::Failure::Source(error)) => {
            report(source_root, error);
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
        Ok(source_commands::Success::Distribution(distribution)) => {
            use std::fmt::Write as _;
            let mut text = String::new();
            for (outcome, probability) in distribution {
                let label: String = outcome
                    .iter()
                    .map(|bit| if *bit { '1' } else { '0' })
                    .collect();
                writeln!(
                    text,
                    "{}: {probability:.12e}",
                    if label.is_empty() { "()" } else { &label }
                )
                .expect("writing to String");
            }
            write_stdout(text.as_bytes(), "distribution")
        }
        Err(source_commands::Failure::Simulation(error)) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
