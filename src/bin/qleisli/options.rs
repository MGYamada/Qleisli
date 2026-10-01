use qleisli::frontend::project::SourcePolicy;
use std::ffi::OsString;
use std::path::PathBuf;

/// Shared by text and machine-readable usage diagnostics.
pub(super) const USAGE: &str = "usage:
  qleisli check <source-root> [--format=json] [source-options]
  qleisli run <source-root> [--format=json] [source-options]
  qleisli sample <source-root> --shots=N --seed=S [--format=json] [source-options]
  qleisli emit-ir <source-root> --output=PATH [--format=json] [source-options]
  qleisli verify-ir <artifact-file> [--against=REQUEST] [--format=json]
  qleisli doc <source-file> [source-options]
  qleisli sized <check|run|sample|emit-proposal> --entry=MODULE::FUNCTION [sized-options]
  qleisli interop <check|run|sample|emit-ir|emit-qasm|emit-qir> <file|-> --input=<qasm|qirf|qli> [--shots=N --seed=S]
  interop always returns JSON; qli input takes a project directory.
source-options: --source-bytes=N --project-bytes=N, or --legacy-source-limits; --qrate
  --qrate selects the explicit [source].root in the selected directory's Qargo.toml.
  Byte limits are positive decimal integers; defaults: 1048576/file, 16777216/project.
  --legacy-source-limits cannot be combined with explicit byte limits.
  --shots: 1..1000000; --seed: 0..18446744073709551615 (decimal, no leading zeros).
  doc produces Markdown text; verify-ir does not accept source-options.";

pub(super) struct Options {
    pub command: String,
    pub path: PathBuf,
    pub policy: SourcePolicy,
    pub shots: Option<u64>,
    pub seed: Option<u64>,
    pub output: Option<PathBuf>,
    pub against: Option<PathBuf>,
    pub qrate: bool,
}

/// Canonical unsigned decimal spelling; the caller supplies its range and type.
pub(super) fn natural<T: std::str::FromStr>(text: &str) -> Option<T> {
    if text.is_empty()
        || !text.bytes().all(|b| b.is_ascii_digit())
        || text.len() > 1 && text.starts_with('0')
    {
        None
    } else {
        text.parse().ok()
    }
}

impl Options {
    pub fn parse(args: &[OsString], json: bool) -> Option<Self> {
        let mut positional = Vec::new();
        let (mut format, mut legacy) = (false, false);
        let (mut source, mut project, mut shots, mut seed) = (None, None, None, None);
        let (mut output, mut against) = (None, None);
        let mut qrate = false;
        for arg in args {
            match arg.to_str() {
                Some("--format=json") if json && !format => format = true,
                Some("--legacy-source-limits") if !legacy => legacy = true,
                Some("--qrate") if !qrate => qrate = true,
                Some(s) if s.starts_with("--source-bytes=") && source.is_none() => {
                    source = Some(natural(&s[15..])?)
                }
                Some(s) if s.starts_with("--project-bytes=") && project.is_none() => {
                    project = Some(natural(&s[16..])?)
                }
                Some(s) if s.starts_with("--shots=") && shots.is_none() => {
                    shots = Some(natural(&s[8..])?)
                }
                Some(s) if s.starts_with("--seed=") && seed.is_none() => {
                    seed = Some(natural(&s[7..])?)
                }
                Some(s) if s.starts_with("--output=") && output.is_none() && s.len() > 9 => {
                    output = Some(PathBuf::from(&s[9..]));
                }
                Some(s) if s.starts_with("--against=") && against.is_none() && s.len() > 10 => {
                    against = Some(PathBuf::from(&s[10..]));
                }
                _ if !arg.as_encoded_bytes().starts_with(b"-") => positional.push(arg),
                _ => return None,
            }
        }
        if format != json
            || positional.len() != 2
            || legacy && (source.is_some() || project.is_some())
            || source == Some(0)
            || project == Some(0)
        {
            return None;
        }
        let command = positional[0].to_str()?;
        if command != "emit-ir" && output.is_some()
            || command != "verify-ir" && against.is_some()
            || matches!(command, "emit-ir" | "verify-ir") && (shots.is_some() || seed.is_some())
            || command == "verify-ir" && (legacy || source.is_some() || project.is_some())
            || matches!(command, "verify-ir" | "doc") && qrate
        {
            return None;
        }
        match command {
            "sample" if shots.is_some_and(|n| (1..=1_000_000).contains(&n)) && seed.is_some() => {}
            "check" | "run" if shots.is_none() && seed.is_none() => {}
            "doc" if !json && shots.is_none() && seed.is_none() => {}
            "emit-ir" if output.is_some() => {}
            "verify-ir" => {}
            _ => return None,
        }
        Some(Self {
            command: command.into(),
            path: PathBuf::from(positional[1]),
            policy: if legacy {
                SourcePolicy::Legacy
            } else {
                SourcePolicy::Bounded {
                    source_bytes: source.unwrap_or(1 << 20),
                    project_bytes: project.unwrap_or(16 << 20),
                }
            },
            shots,
            seed,
            output,
            against,
            qrate,
        })
    }
}
