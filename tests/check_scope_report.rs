//! Native decision observations cannot turn partial contracts into source proofs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ProjectCheckReport, check_project_report_with_kernel};
use qleisli::frontend::project::{QrateSource, SourcePolicy};
use qleisli::interchange::native::Kernel;

fn report(source: &str) -> ProjectCheckReport {
    let root = SourceRoot::new(source);
    check_project_report_with_kernel(&root.0, SourcePolicy::Legacy, &Kernel::selected().unwrap())
        .unwrap()
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn entry_and_library_reports_describe_actual_concrete_roots() {
    let library = report("pub classical fn identity(x: Bit) -> Bit { x }");
    let entry = report("observe fn main() -> Bit { 0 }");
    assert_eq!(library.entry_request_checked(), None);
    assert_eq!(entry.entry_request_checked(), Some(false));
    assert_eq!(library.concrete_local_roots(), 0);
    assert_eq!(entry.concrete_local_roots(), 1);
    assert!(library.concrete_bundled_roots() > 0);
    assert_eq!(
        entry.concrete_bundled_roots(),
        library.concrete_bundled_roots()
    );
    for checked in [&entry, &library] {
        let decisions = checked.native_decisions();
        assert!(decisions.complete());
        assert_eq!(decisions.requests_checked(), 0);
        // Lowering and dependency checks can make additional native decisions;
        // a concrete source root count is not an invocation count.
        assert!(
            decisions.decisions()
                >= checked.concrete_local_roots() + checked.concrete_bundled_roots()
        );
        let expected = std::fs::canonicalize(std::env::var_os("QLEISLI_KERNEL").unwrap()).unwrap();
        assert_eq!(
            decisions.checker_paths().collect::<Vec<_>>(),
            vec![expected.as_path()]
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn unused_finite_meaning_is_not_a_native_request() {
    let ordinary = report("observe fn main() -> Bit { 0 }");
    let unused = report(
        "classical fn flip(x:Bit)->Bit{not x}
         meaning Flip:Bit=permutation_by(flip);
         observe fn main()->Bit{0}",
    );
    assert_eq!(unused.native_decisions().requests_checked(), 0);
    assert_eq!(
        unused.native_decisions().decisions(),
        ordinary.native_decisions().decisions()
    );
    assert_eq!(unused.entry_request_checked(), Some(false));
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn reference_meaning_requests_do_not_promote_the_entry() {
    let checked = report(
        "
         unitary fn reference_h(q:Q<Bit>)->Q<Bit>{h(q)}
         meaning H:Bit=reference(reference_h);
         observe fn main()->Bit{0}",
    );
    assert_eq!(checked.entry_request_checked(), Some(false));
    assert!(checked.native_decisions().requests_checked() > 0);
    assert!(
        checked.native_decisions().decisions()
            > checked.concrete_local_roots() + checked.concrete_bundled_roots()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn operation_instantiations_stay_within_concrete_roots_and_selected_qrate() {
    let root = SourceRoot::new(
        "use std::gate::x; use std::state::init0; 
         unitary fn identity(q:Q<Bit>)->Q<Bit>{q}
         unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)}
         unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         observe fn main()->Bit{measure_z(apply[flip](apply[identity](init0())))}",
    );
    std::fs::create_dir(root.0.join("src")).unwrap();
    std::fs::rename(root.0.join("main.qli"), root.0.join("src/main.qli")).unwrap();
    root.write(
        "Qargo.toml",
        "schema-version = 2\n[qrate]\nedition = \"2026\"\n[source]\nroot = \"src\"\n",
    );
    let selected = QrateSource::select(&root.0).unwrap();
    let checked = selected
        .check_report_with_kernel(SourcePolicy::Legacy, &Kernel::selected().unwrap())
        .unwrap();
    assert_eq!(checked.concrete_local_roots(), 3);
    assert_eq!(checked.entry_request_checked(), Some(false));
    assert_eq!(checked.native_decisions().requests_checked(), 0);
}
