//! Host adapter exercise; output is text on stdout, with no backend submission.
use qleisli_core::frontend::compile::compile_project;
use qleisli_core::interop::{
    MAX_OPENQASM_BYTES, export_openqasm3, export_qir_base, import_openqasm3,
};
use qleisli_core::sim::{SimulationLimits, run_closed};
use std::fmt::Write as _;
use std::io::{Read, Write};
use std::path::Path;

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() != 2 {
        return Err("usage: interop <qasm-check|qasm-run|qasm-canonical|qasm-to-qir|qli-to-qasm|qli-to-qir> <path>".into());
    }
    let mode = args[0].to_str().ok_or("mode must be UTF-8")?;
    if !matches!(
        mode,
        "qasm-check" | "qasm-run" | "qasm-canonical" | "qasm-to-qir" | "qli-to-qasm" | "qli-to-qir"
    ) {
        return Err("unknown interop mode".into());
    }
    let path = Path::new(&args[1]);
    let program = if mode.starts_with("qli-") {
        compile_project(path)?
    } else {
        let mut bytes = Vec::new();
        std::fs::File::open(path)?
            .take((MAX_OPENQASM_BYTES + 1) as u64)
            .read_to_end(&mut bytes)?;
        if bytes.len() > MAX_OPENQASM_BYTES {
            return Err("OpenQASM input exceeds 1 MiB".into());
        }
        import_openqasm3(std::str::from_utf8(&bytes)?)?
    };
    let text = match mode {
        "qasm-check" => "verified terminal-profile IR\n".to_owned(),
        "qasm-run" => {
            let results = run_closed(&program, SimulationLimits::default())?;
            let mut text = String::new();
            for (bits, probability) in results {
                writeln!(text, "{bits:?}: {probability:.16}")?;
            }
            text
        }
        "qasm-canonical" | "qli-to-qasm" => export_openqasm3(&program)?,
        _ => export_qir_base(&program)?,
    };
    std::io::stdout().lock().write_all(text.as_bytes())?;
    Ok(())
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            std::process::ExitCode::FAILURE
        }
    }
}
