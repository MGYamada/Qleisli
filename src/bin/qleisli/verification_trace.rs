//! Machine-readable observations emitted only when explicitly requested.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use std::io::{self, Write};
use std::process::ExitCode;

use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::verification_trace::Trace;

use super::json::quoted;
use super::source_commands::{Failure, Outcome};

pub(super) struct Command {
    pub route: &'static str,
    policy: Option<SourcePolicy>,
    diagnostic: Option<&'static str>,
}

impl Default for Command {
    fn default() -> Self {
        Self {
            route: "usage",
            policy: None,
            diagnostic: None,
        }
    }
}

impl Command {
    pub fn source(&mut self, outcome: &Outcome) {
        self.route = match outcome.command.as_str() {
            "check" => "check",
            "run" => "run",
            "sample" => "sample",
            "doc" => "doc",
            "emit-ir" => "emit-ir",
            "verify-ir" => "verify-ir",
            _ => "usage",
        };
        self.policy = outcome.policy;
        self.diagnostic = outcome.result.as_ref().err().map(|error| match error {
            Failure::Source(error) | Failure::Simulation(error) => error.code,
            Failure::Artifact(error) => error.code,
        });
    }

    pub fn write(self, status: ExitCode, trace: Trace) {
        let policy = match self.policy {
            None => "null".to_owned(),
            Some(SourcePolicy::Legacy) => "{\"policy\":\"legacy\"}".to_owned(),
            Some(SourcePolicy::Bounded {
                source_bytes,
                project_bytes,
            }) => format!(
                "{{\"policy\":\"bounded\",\"source_bytes\":{source_bytes},\"project_bytes\":{project_bytes}}}"
            ),
        };
        let requests = trace
            .requests
            .into_iter()
            .map(|request| {
                format!(
                    "{{\"request_sha256\":{},\"subject_sha256\":{},\"obligation\":{},\"edition\":{},\"scope\":{},\"decision\":{},\"diagnostic\":{}}}",
                    quoted(&request.identity),
                    text(request.subject.as_deref()),
                    quoted(request.obligation),
                    request.edition.map_or_else(|| "null".to_owned(), |value| value.to_string()),
                    text(request.scope),
                    quoted(request.decision),
                    text(request.diagnostic),
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(
            io::stderr().lock(),
            "{{\"format\":\"qleisli.verification-trace\",\"version\":1,\"route\":{},\"source_policy\":{policy},\"success\":{},\"diagnostic\":{},\"native_protocol\":\"qleisli.native-result 4\",\"product\":{},\"requests\":[{requests}],\"omitted\":{}}}",
            quoted(self.route),
            status == ExitCode::SUCCESS,
            text(self.diagnostic),
            quoted(env!("CARGO_PKG_VERSION")),
            trace.omitted,
        );
    }
}

fn text(value: Option<&str>) -> String {
    value.map_or_else(|| "null".to_owned(), quoted)
}
