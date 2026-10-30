//! Strict native reply context. Parsed context alone issues no accepted handle.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::native_packet::Scope;
use super::{Error, Result};
use crate::edition::Edition;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Mode {
    Ordinary,
    Contract,
    CarrierPure,
    OrdinaryRoot,
    RuntimeRoot,
    QmatchSource,
    Hierarchy,
    HierarchyRequest,
    HierarchyFourier,
    Instrument,
    QpeInstrument,
    EngineeringPure,
    EngineeringPureTensor,
    EngineeringInstrument,
    EngineeringOpenQasm,
    Readout,
    Preparation,
}

impl Mode {
    pub(super) fn argument(self) -> &'static str {
        match self {
            Self::Ordinary => "--qirf-native",
            Self::Contract => "--qirf-contract",
            Self::CarrierPure => "--carrier-pure-check",
            Self::OrdinaryRoot => "--ordinary-root-check",
            Self::RuntimeRoot => "--runtime-root-check",
            Self::QmatchSource => "--qmatch-source-check",
            Self::Hierarchy => "--hierarchy-pending",
            Self::HierarchyRequest => "--hierarchy-request-pending",
            Self::HierarchyFourier => "--hierarchy-fourier-pending",
            Self::Instrument => "--instrument-pending",
            Self::QpeInstrument => "--qpe-instrument-pending",
            Self::EngineeringPure => "--engineering-pure-check",
            Self::EngineeringPureTensor => "--engineering-pure-tensor-check",
            Self::EngineeringInstrument => "--qirf-engineering-instrument-native",
            Self::EngineeringOpenQasm => "--engineering-openqasm-check",
            Self::Readout => "--readout-check",
            Self::Preparation => "--preparation-check",
        }
    }

    pub(super) fn parse(argument: &str) -> Result<Self> {
        match argument {
            "--qirf-native" => Ok(Self::Ordinary),
            "--qirf-contract" => Ok(Self::Contract),
            "--carrier-pure-check" => Ok(Self::CarrierPure),
            "--ordinary-root-check" => Ok(Self::OrdinaryRoot),
            "--runtime-root-check" => Ok(Self::RuntimeRoot),
            "--qmatch-source-check" => Ok(Self::QmatchSource),
            "--hierarchy-pending" => Ok(Self::Hierarchy),
            "--hierarchy-request-pending" => Ok(Self::HierarchyRequest),
            "--hierarchy-fourier-pending" => Ok(Self::HierarchyFourier),
            "--instrument-pending" => Ok(Self::Instrument),
            "--qpe-instrument-pending" => Ok(Self::QpeInstrument),
            "--engineering-pure-check" => Ok(Self::EngineeringPure),
            "--engineering-pure-tensor-check" => Ok(Self::EngineeringPureTensor),
            "--qirf-engineering-instrument-native" => Ok(Self::EngineeringInstrument),
            "--engineering-openqasm-check" => Ok(Self::EngineeringOpenQasm),
            "--readout-check" => Ok(Self::Readout),
            "--preparation-check" => Ok(Self::Preparation),
            _ => Err(Error::format("unknown native mode")),
        }
    }

    fn status(self) -> &'static str {
        match self {
            Self::Ordinary
            | Self::Contract
            | Self::CarrierPure
            | Self::OrdinaryRoot
            | Self::RuntimeRoot
            | Self::QmatchSource => "accepted",
            Self::Hierarchy
            | Self::HierarchyRequest
            | Self::HierarchyFourier
            | Self::Instrument
            | Self::QpeInstrument => "pending",
            Self::EngineeringPure
            | Self::EngineeringPureTensor
            | Self::EngineeringInstrument
            | Self::EngineeringOpenQasm => "engineering-checked",
            Self::Readout | Self::Preparation => "checked",
        }
    }

    fn permits(self, scope: Scope) -> bool {
        match self {
            Self::Ordinary | Self::Contract => true,
            Self::Hierarchy
            | Self::HierarchyRequest
            | Self::HierarchyFourier
            | Self::Instrument
            | Self::QpeInstrument => scope != Scope::Caller,
            Self::CarrierPure
            | Self::OrdinaryRoot
            | Self::RuntimeRoot
            | Self::QmatchSource
            | Self::EngineeringPure
            | Self::EngineeringPureTensor
            | Self::EngineeringInstrument
            | Self::EngineeringOpenQasm => scope == Scope::Execution,
            Self::Readout | Self::Preparation => scope == Scope::Inspection,
        }
    }
}

/// Context read from a fresh successful reply and matched against the invocation.
/// Its constructor is private; it cannot authorize a subject without its payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedContext {
    edition: Edition,
    mode: Mode,
    scope: Scope,
}

impl CheckedContext {
    pub(super) fn edition(self) -> Edition {
        self.edition
    }

    pub(super) fn mode(self) -> &'static str {
        self.mode.argument()
    }

    pub(super) fn scope(self) -> Scope {
        self.scope
    }
}

pub(super) enum Reply<'a> {
    Rejected(&'static str),
    Checked {
        context: CheckedContext,
        payload: Vec<&'a str>,
    },
}

/// Require the one current frame before a profile interprets its own payload.
/// No old reply, mismatched claim, implicit edition or trailing frame is accepted.
pub(super) fn parse(bytes: &[u8], edition: Edition, mode: Mode, scope: Scope) -> Result<Reply<'_>> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| Error::format("invalid native response UTF-8"))?;
    let fields: Vec<_> = text.split('\n').collect();
    if fields.first() != Some(&"qleisli.native-result 3") {
        return Err(Error::format("unknown native response protocol"));
    }
    if let [_, "error", code, ""] = fields.as_slice() {
        return Ok(Reply::Rejected(match *code {
            "format" => "format",
            "limit" => "limit",
            "contract" => "contract",
            "invalid_ir" => "invalid_ir",
            "decoded_view" => "decoded_view",
            "version" => "version",
            "edition" => "edition",
            _ => return Err(Error::format("unknown native rejection")),
        }));
    }
    if fields.len() < 8 || fields.last() != Some(&"") {
        return Err(Error::format("truncated or trailing native response"));
    }
    if !mode.permits(scope)
        || fields[1] != mode.status()
        || fields[2] != edition.as_str()
        || fields[3] != env!("CARGO_PKG_VERSION")
        || fields[4] != mode.argument()
        || fields[5] != scope.name()
    {
        return Err(Error::format(
            "native reply context disagrees with the invocation",
        ));
    }
    Ok(Reply::Checked {
        context: CheckedContext {
            edition,
            mode,
            scope,
        },
        payload: fields[6..fields.len() - 1].to_vec(),
    })
}

#[derive(Debug)]
pub(super) struct WorkDecision {
    pub(super) context: CheckedContext,
    pub(super) exact_work: usize,
}

pub(super) fn engineering_response(
    bytes: &[u8],
    edition: Edition,
    mode: Mode,
) -> Result<WorkDecision> {
    if !matches!(
        mode,
        Mode::EngineeringPure
            | Mode::EngineeringPureTensor
            | Mode::EngineeringInstrument
            | Mode::EngineeringOpenQasm
    ) {
        return Err(Error::format(
            "engineering comparison requires an engineering native mode",
        ));
    }
    let (context, payload) = match parse(bytes, edition, mode, Scope::Execution)? {
        Reply::Checked { context, payload } => (context, payload),
        Reply::Rejected(code) => {
            let code = if code == "version" { "kernel" } else { code };
            return Err(Error::new(
                code,
                if code == "kernel" {
                    "native checker product version differs from the Rust package"
                } else {
                    "Lean engineering checker rejected the artifact/request; no fallback"
                },
            ));
        }
    };
    let [work] = payload.as_slice() else {
        return Err(Error::format("malformed/trailing engineering response"));
    };
    if work.is_empty()
        || work.len() > 8
        || !work.bytes().all(|b| b.is_ascii_digit())
        || work.len() > 1 && work.starts_with('0')
    {
        return Err(Error::format("noncanonical engineering work count"));
    }
    let exact_work = work
        .parse()
        .map_err(|_| Error::format("invalid engineering work count"))?;
    if exact_work > crate::contract::DEFAULT_EXACT_WORK {
        return Err(Error::format("engineering work bound disagrees"));
    }
    Ok(WorkDecision {
        context,
        exact_work,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_mode_requires_its_own_explicit_context_and_claim_class() {
        for mode in [
            Mode::Ordinary,
            Mode::Contract,
            Mode::CarrierPure,
            Mode::OrdinaryRoot,
            Mode::RuntimeRoot,
            Mode::QmatchSource,
            Mode::Hierarchy,
            Mode::HierarchyRequest,
            Mode::HierarchyFourier,
            Mode::Instrument,
            Mode::QpeInstrument,
            Mode::EngineeringPure,
            Mode::EngineeringPureTensor,
            Mode::EngineeringInstrument,
            Mode::EngineeringOpenQasm,
            Mode::Readout,
            Mode::Preparation,
        ] {
            assert_eq!(Mode::parse(mode.argument()).unwrap(), mode);
            let scope = if matches!(
                mode,
                Mode::CarrierPure
                    | Mode::OrdinaryRoot
                    | Mode::RuntimeRoot
                    | Mode::QmatchSource
                    | Mode::EngineeringPure
                    | Mode::EngineeringPureTensor
                    | Mode::EngineeringInstrument
                    | Mode::EngineeringOpenQasm
            ) {
                Scope::Execution
            } else {
                Scope::Inspection
            };
            let good = format!(
                "qleisli.native-result 3\n{}\n2026\n{}\n{}\n{}\n0\n",
                mode.status(),
                env!("CARGO_PKG_VERSION"),
                mode.argument(),
                scope.name()
            );
            let Reply::Checked { context, payload } =
                parse(good.as_bytes(), Edition::E2026, mode, scope).unwrap()
            else {
                panic!("valid explicit context rejected")
            };
            assert_eq!(context.edition(), Edition::E2026);
            assert_eq!(context.mode(), mode.argument());
            assert_eq!(payload, ["0"]);
            for changed in [
                good.replace("result 3", "result 2"),
                good.replace("\n2026\n", "\n2027\n"),
                good.replace("\n2026\n", "\n02026\n"),
                good.replace(env!("CARGO_PKG_VERSION"), "0.3.0-alpha"),
                good.replace(mode.argument(), "--unknown-native-mode"),
                good.replace(
                    &format!("\n{}\n", scope.name()),
                    if scope == Scope::Inspection {
                        "\nexecution\n"
                    } else {
                        "\ninspection\n"
                    },
                ),
                good.replace(mode.status(), "unverified"),
                good.trim_end().to_owned(),
            ] {
                assert!(parse(changed.as_bytes(), Edition::E2026, mode, scope).is_err());
            }
        }
    }

    #[test]
    fn failures_have_no_success_context_and_legacy_frames_never_fall_back() {
        for code in [
            "format",
            "limit",
            "contract",
            "invalid_ir",
            "decoded_view",
            "version",
            "edition",
        ] {
            let frame = format!("qleisli.native-result 3\nerror\n{code}\n");
            assert!(
                matches!(parse(frame.as_bytes(), Edition::E2026, Mode::Ordinary, Scope::Inspection),
                Ok(Reply::Rejected(actual)) if actual == code)
            );
            assert!(
                parse(
                    format!("{frame}extra\n").as_bytes(),
                    Edition::E2026,
                    Mode::Ordinary,
                    Scope::Inspection
                )
                .is_err()
            );
        }
        for frame in [
            "qleisli.qirf-native 2\naccepted\ninspection\n1\n0\n",
            "qleisli.native-result 3\nerror\nunknown\n",
            "qleisli.native-result 3\nerror\nformat",
        ] {
            assert!(
                parse(
                    frame.as_bytes(),
                    Edition::E2026,
                    Mode::Ordinary,
                    Scope::Inspection
                )
                .is_err()
            );
        }
    }
}
