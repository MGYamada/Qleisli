//! First native-only artifact-to-handle route. No legacy verifier is invoked.
//! Usage: native_acceptance KERNEL ARTIFACT [REQUEST]
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::native::{Kernel, Proposal};

fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if !(2..=3).contains(&args.len()) {
        eprintln!("usage: native_acceptance KERNEL ARTIFACT [REQUEST]");
        return std::process::ExitCode::from(2);
    }
    let bytes = match std::fs::read(&args[1]) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("{error}");
            return std::process::ExitCode::from(2);
        }
    };
    let request = match args.get(2).map(std::fs::read).transpose() {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("{error}");
            return std::process::ExitCode::from(2);
        }
    };
    match Proposal::new(&bytes, request.as_deref()).and_then(|p| Kernel::new(&args[0]).accept(&p)) {
        Ok(_) => {
            println!("accepted");
            std::process::ExitCode::SUCCESS
        }
        Err(error) => {
            println!("error\t{}", error.code);
            eprintln!("{error}");
            std::process::ExitCode::FAILURE
        }
    }
}
