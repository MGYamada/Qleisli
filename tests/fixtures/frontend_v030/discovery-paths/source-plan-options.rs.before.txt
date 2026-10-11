//! One argument contract for selected-source execution and its legacy adapter.

use std::{collections::BTreeMap, ffi::OsString, path::PathBuf};

use super::super::options::natural;

pub(super) const USAGE: &str =
    "usage: qleisli <check|run|sample|emit-proposal> --entry=module::function
  --module=name=PATH (repeat) --nat=name=N (repeat)
  [--operation=name=module::function --operation-nat=name.parameter=N] (repeat)
  [--ir-profile=auto|raw|hierarchy] [--lean-kernel=PATH]
  [--request=PATH | --qpe-provider=PATH] [--format=json]
  [--basis=N] [--shots=N --seed=N] [--output=PATH]
  --kernel is an alias for --lean-kernel; otherwise use QLEISLI_KERNEL.
  Raw run/sample require zero runtime parameters and no quantum result.
  --basis is hierarchy run/sample-only (default 0); it is never ordinary input.
  Selected-source sample requires shots in 1..1024 and a seed.
  emit-proposal requires output and no kernel/request/provider; it is untrusted.
  Module-map checking covers every declaration, native checking the selected instance.";

#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum IrProfile {
    #[default]
    Auto,
    Raw,
    Hierarchy,
}

#[derive(Default)]
pub(super) struct Options {
    pub command: String,
    pub entry: String,
    pub modules: BTreeMap<String, PathBuf>,
    pub ns: BTreeMap<String, u32>,
    pub ops: BTreeMap<String, String>,
    pub op_ns: BTreeMap<String, BTreeMap<String, u32>>,
    pub kernel: Option<PathBuf>,
    pub request: Option<PathBuf>,
    pub provider: Option<PathBuf>,
    pub output: Option<PathBuf>,
    pub basis: Option<usize>,
    pub shots: Option<usize>,
    pub seed: Option<u64>,
    pub ir_profile: IrProfile,
}

/// Flags selecting this input form, including malformed/incomplete requests.
/// These never fall through to a project execution after selected parsing fails.
pub(super) fn selected(args: &[OsString]) -> bool {
    args.iter().any(|arg| {
        arg.to_str().is_some_and(|arg| {
            [
                "--entry",
                "--module",
                "--nat",
                "--operation",
                "--operation-nat",
                "--ir-profile",
                "--request",
                "--qpe-provider",
                "--basis",
                "--kernel",
            ]
            .iter()
            .any(|flag| arg == *flag || arg.strip_prefix(flag).is_some_and(|s| s.starts_with('=')))
        })
    })
}

pub(super) fn parse(args: &[OsString]) -> Option<Options> {
    let mut result = Options::default();
    let mut singleton = std::collections::BTreeSet::new();
    let mut positional = Vec::new();
    for arg in args {
        let text = arg.to_str()?;
        if !text.starts_with('-') {
            positional.push(text);
            continue;
        }
        let (flag, value) = text.strip_prefix("--")?.split_once('=')?;
        let flag = if flag == "kernel" {
            "lean-kernel"
        } else {
            flag
        };
        if value.is_empty()
            || !matches!(flag, "module" | "nat" | "operation" | "operation-nat")
                && !singleton.insert(flag)
        {
            return None;
        }
        match flag {
            "entry" => result.entry = value.into(),
            "module" => {
                let (key, path) = value.split_once('=')?;
                if key.is_empty()
                    || path.is_empty()
                    || result.modules.insert(key.into(), path.into()).is_some()
                {
                    return None;
                }
            }
            "nat" => {
                let (key, value) = value.split_once('=')?;
                if key.is_empty() || result.ns.insert(key.into(), natural(value)?).is_some() {
                    return None;
                }
            }
            "operation" => {
                let (key, definition) = value.split_once('=')?;
                if key.is_empty()
                    || definition.is_empty()
                    || result.ops.insert(key.into(), definition.into()).is_some()
                {
                    return None;
                }
            }
            "operation-nat" => {
                let (key, value) = value.split_once('=')?;
                let (operation, name) = key.split_once('.')?;
                if operation.is_empty()
                    || name.is_empty()
                    || result
                        .op_ns
                        .entry(operation.into())
                        .or_default()
                        .insert(name.into(), natural(value)?)
                        .is_some()
                {
                    return None;
                }
            }
            "lean-kernel" => result.kernel = Some(value.into()),
            "request" => result.request = Some(value.into()),
            "qpe-provider" => result.provider = Some(value.into()),
            "output" => result.output = Some(value.into()),
            "basis" => result.basis = Some(natural(value)?),
            "shots" => result.shots = Some(natural(value)?),
            "seed" => result.seed = Some(natural(value)?),
            "ir-profile" => {
                result.ir_profile = match value {
                    "auto" => IrProfile::Auto,
                    "raw" => IrProfile::Raw,
                    "hierarchy" => IrProfile::Hierarchy,
                    _ => return None,
                }
            }
            "format" if value == "json" => {}
            _ => return None,
        }
    }
    if positional.len() != 1
        || result.entry.is_empty()
        || result.modules.is_empty()
        || result.request.is_some() && result.provider.is_some()
        || result.op_ns.keys().any(|key| !result.ops.contains_key(key))
        || result.ir_profile == IrProfile::Raw
            && (result.request.is_some() || result.provider.is_some())
    {
        return None;
    }
    result.command = positional[0].into();
    match result.command.as_str() {
        "emit-proposal"
            if result.output.is_some()
                && result.kernel.is_none()
                && result.request.is_none()
                && result.provider.is_none()
                && result.shots.is_none()
                && result.seed.is_none()
                && result.basis.is_none() => {}
        "check" | "run"
            if result.output.is_none()
                && result.shots.is_none()
                && result.seed.is_none()
                && (result.command == "run" || result.basis.is_none()) => {}
        "sample"
            if result.output.is_none()
                && result.shots.is_some_and(|n| (1..=1024).contains(&n))
                && result.seed.is_some() => {}
        _ => return None,
    }
    Some(result)
}
