//! Transitional argument adapter. Preparation and execution are shared with
//! the ordinary selected-source command namespace.
use std::{ffi::OsString, process::ExitCode};

pub(super) fn run(args: &[OsString]) -> ExitCode {
    super::source_plan::run(args, true)
}
