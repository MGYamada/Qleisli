//! Bounded explicit direct-native client. No source or producer authority.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::{self, hierarchical::Kernel};
use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const MAX_FILE_BYTES: u64 = 1 << 20;
const USAGE: &str = "usage: qleisli-qft-native-gate-design inspect KERNEL PAYLOAD | request KERNEL PAYLOAD REQUEST; KERNEL must be an absolute path";

#[derive(Clone, Copy)]
enum Action {
    Inspect,
    Request,
}
impl Action {
    fn name(self) -> &'static str {
        match self {
            Self::Inspect => "inspect",
            Self::Request => "request",
        }
    }
}

struct Options {
    action: Action,
    kernel: PathBuf,
    payload: PathBuf,
    request: Option<PathBuf>,
}

struct Failure {
    stage: &'static str,
    code: &'static str,
    message: String,
    json_pointer: String,
    exit: u8,
}
impl Failure {
    fn local(stage: &'static str, code: &'static str, message: impl Into<String>) -> Self {
        Self {
            stage,
            code,
            message: message.into(),
            json_pointer: String::new(),
            exit: 2,
        }
    }

    fn kernel(error: interchange::Error) -> Self {
        Self {
            stage: "hierarchical-kernel-api",
            code: error.code,
            message: error.message,
            json_pointer: error.json_pointer,
            exit: 1,
        }
    }
}

fn parse(args: &[OsString]) -> Result<Options, Failure> {
    let (action, kernel, payload, request) = match args {
        [action, kernel, payload] if action == "inspect" => {
            (Action::Inspect, kernel, payload, None)
        }
        [action, kernel, payload, request] if action == "request" => {
            (Action::Request, kernel, payload, Some(request))
        }
        _ => return Err(Failure::local("arguments", "usage", USAGE)),
    };
    let kernel = PathBuf::from(kernel);
    if !kernel.is_absolute() {
        return Err(Failure::local("arguments", "usage", USAGE));
    }
    Ok(Options {
        action,
        kernel,
        payload: PathBuf::from(payload),
        request: request.map(PathBuf::from),
    })
}

fn read_bounded(path: &Path, name: &str) -> Result<Vec<u8>, Failure> {
    let file = File::open(path)
        .map_err(|error| Failure::local("input", "io", format!("{name}: {error}")))?;
    let metadata = file
        .metadata()
        .map_err(|error| Failure::local("input", "io", format!("{name}: {error}")))?;
    if !metadata.is_file() {
        return Err(Failure::local(
            "input",
            "io",
            format!("{name}: expected a regular file"),
        ));
    }
    if metadata.len() > MAX_FILE_BYTES {
        return Err(Failure::local(
            "input",
            "limit",
            format!("{name}: exceeds 1 MiB"),
        ));
    }
    let mut bytes = Vec::new();
    file.take(MAX_FILE_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| Failure::local("input", "io", format!("{name}: {error}")))?;
    if bytes.len() as u64 > MAX_FILE_BYTES {
        return Err(Failure::local(
            "input",
            "limit",
            format!("{name}: exceeds 1 MiB"),
        ));
    }
    Ok(bytes)
}

fn quote(value: &str) -> String {
    let mut out = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if c <= '\u{1f}' => {
                write!(&mut out, "\\u{:04x}", c as u32).expect("String formatting cannot fail");
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn check(options: &Options) -> Result<String, Failure> {
    let payload = read_bounded(&options.payload, "payload")?;
    let request = options
        .request
        .as_deref()
        .map(|path| read_bounded(path, "request"))
        .transpose()?;
    let kernel = Kernel::new(options.kernel.clone());
    let checked = match options.action {
        Action::Inspect => kernel.inspect_native(&payload),
        Action::Request => kernel.check_against_native(
            &payload,
            request
                .as_deref()
                .expect("request action requires a request"),
        ),
    }
    .map_err(Failure::kernel)?;

    // Test the immutable native report; never reserialize or derive a request
    // from its candidate meanings. Panic diagnostics do not print input bytes.
    assert!(
        checked.payload() == payload.as_slice(),
        "native report substituted payload bytes"
    );
    assert!(
        checked.request() == request.as_deref(),
        "native report substituted request bytes"
    );
    assert!(checked.candidate().is_none(), "unexpected candidate report");
    assert!(!checked.is_instrument(), "unexpected instrument report");

    let request_bytes = request
        .as_ref()
        .map_or_else(|| "null".to_owned(), |bytes| bytes.len().to_string());
    Ok(format!(
        "{{\"action\":{},\"status\":\"ok\",\"payload_bytes\":{},\"request_bytes\":{},\"retained_payload_equal\":true,\"retained_request_equal\":true,\"structural_work\":{},\"exact_work\":{}}}",
        quote(options.action.name()),
        payload.len(),
        request_bytes,
        checked.structural_work(),
        checked.exact_work(),
    ))
}

fn error_record(action: Option<Action>, failure: &Failure) -> String {
    let action = action.map_or_else(|| "null".to_owned(), |action| quote(action.name()));
    format!(
        "{{\"action\":{action},\"status\":\"error\",\"stage\":{},\"code\":{},\"message\":{},\"json_pointer\":{}}}",
        quote(failure.stage),
        quote(failure.code),
        quote(&failure.message),
        quote(&failure.json_pointer),
    )
}

fn main() -> ExitCode {
    // Six is enough to reject every surplus-argument form without retaining an
    // unbounded argument vector. No commands or paths are read from artifacts.
    let args: Vec<_> = std::env::args_os().skip(1).take(6).collect();
    let options = match parse(&args) {
        Ok(options) => options,
        Err(failure) => {
            println!("{}", error_record(None, &failure));
            return ExitCode::from(failure.exit);
        }
    };
    match check(&options) {
        Ok(record) => {
            println!("{record}");
            ExitCode::SUCCESS
        }
        Err(failure) => {
            println!("{}", error_record(Some(options.action), &failure));
            ExitCode::from(failure.exit)
        }
    }
}
