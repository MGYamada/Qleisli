//! Sized CLI argument validation, separate from checking and execution.

use std::{collections::BTreeMap, ffi::OsString, path::PathBuf};

use super::super::options::natural;

pub(super) const USAGE: &str =
    "usage: qleisli sized <check|run|sample|emit-proposal> --entry=module::function
  --module=name=PATH (repeat) --nat=name=N (repeat)
  [--operation=name=module::function --operation-nat=name.parameter=N] (repeat)
  --kernel=PATH [--request=PATH | --qpe-provider=PATH]
  [--basis=N] [--shots=N --seed=N] [--output=PATH]
  --basis is run/sample-only (default 0). sample requires shots and seed.
  emit-proposal requires output and no kernel; it emits untrusted JSON.
  default check/run/sample verify producer consistency, not source meaning.
  --request verifies the IR against a caller-supplied composition contract;
  --qpe-provider verifies the named QPE contract. Every result reports this scope.
  The legacy check status means checked IR; none of these modes proves source preservation.";

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
    pub basis: usize,
    pub shots: Option<usize>,
    pub seed: Option<u64>,
}
pub(super) fn parse(args: &[OsString]) -> Option<Options> {
    let mut result = Options {
        command: args.first()?.to_str()?.into(),
        ..Options::default()
    };
    let mut singleton = std::collections::BTreeSet::new();
    for a in &args[1..] {
        let (flag, value) = a.to_str()?.strip_prefix("--")?.split_once('=')?;
        if value.is_empty() {
            return None;
        }
        if !matches!(flag, "module" | "nat" | "operation" | "operation-nat")
            && !singleton.insert(flag)
        {
            return None;
        }
        match flag {
            "entry" => result.entry = value.into(),
            "module" => {
                let (k, v) = value.split_once('=')?;
                if v.is_empty() || result.modules.insert(k.into(), v.into()).is_some() {
                    return None;
                }
            }
            "nat" => {
                let (k, v) = value.split_once('=')?;
                if result.ns.insert(k.into(), natural(v)?).is_some() {
                    return None;
                }
            }
            "operation" => {
                let (k, v) = value.split_once('=')?;
                if result.ops.insert(k.into(), v.into()).is_some() {
                    return None;
                }
            }
            "operation-nat" => {
                let (key, v) = value.split_once('=')?;
                let (op, k) = key.split_once('.')?;
                if result
                    .op_ns
                    .entry(op.into())
                    .or_default()
                    .insert(k.into(), natural(v)?)
                    .is_some()
                {
                    return None;
                }
            }
            "kernel" => result.kernel = Some(value.into()),
            "request" => result.request = Some(value.into()),
            "qpe-provider" => result.provider = Some(value.into()),
            "output" => result.output = Some(value.into()),
            "basis" => result.basis = natural(value)?,
            "shots" => result.shots = Some(natural(value)?),
            "seed" => result.seed = Some(natural(value)?),
            _ => return None,
        }
    }
    if result.entry.is_empty()
        || result.modules.is_empty()
        || result.request.is_some() && result.provider.is_some()
        || result.op_ns.keys().any(|k| !result.ops.contains_key(k))
    {
        return None;
    }
    match result.command.as_str() {
        "emit-proposal"
            if result.output.is_some()
                && result.kernel.is_none()
                && result.request.is_none()
                && result.provider.is_none()
                && result.shots.is_none()
                && result.seed.is_none()
                && !singleton.contains("basis") => {}
        "check" | "run"
            if result.kernel.is_some()
                && result.output.is_none()
                && result.shots.is_none()
                && result.seed.is_none()
                && (result.command == "run" || !singleton.contains("basis")) => {}
        "sample"
            if result.kernel.is_some()
                && result.output.is_none()
                && result.shots.is_some_and(|n| (1..=1024).contains(&n))
                && result.seed.is_some() => {}
        _ => return None,
    }
    Some(result)
}
