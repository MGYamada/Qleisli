//! Bind each original control role to its ordered, replayed hierarchy interval.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::super::raw::{control_subjects, finite_basis};
use super::*;
use crate::contract::{DEFAULT_EXACT_WORK, exact::Budget};
use crate::frontend::ast::QuantumAccess;
use crate::interchange::hierarchical::ControlRequest;

pub(super) fn eligible(source: &ElaboratedProgram, profile: Effect) -> Result<()> {
    if !source.has_control_obligations() {
        return Ok(());
    }
    if profile != Effect::Unitary || source.has_operation_meanings() {
        return source.require_control_evidence();
    }
    control_subjects(source, &mut Budget::new(DEFAULT_EXACT_WORK))?;
    Ok(())
}

pub(super) fn requests(proposal: &HierarchyProposal) -> Result<Vec<ControlRequest>> {
    let source = proposal.source();
    if !source.has_control_obligations() {
        return Ok(Vec::new());
    }
    if proposal.is_instrument() {
        return Err(preservation::invalid(
            "source control requires a pure hierarchy",
        ));
    }
    zero_basis::validate(proposal)?;
    let subjects = control_subjects(source, &mut Budget::new(DEFAULT_EXACT_WORK))?;
    let mut requests = Vec::new();
    for subject in subjects {
        let trace = proposal
            .pure_traces
            .iter()
            .find(|trace| trace.definition == subject)
            .ok_or_else(|| {
                preservation::invalid("original control body lacks its reachable trace")
            })?;
        let steps = source.definitions()[subject].steps();
        for (step, event) in steps.iter().zip(&trace.events) {
            if !step.needs_control_check() {
                continue;
            }
            let root = event.unitary_definition().ok_or_else(|| {
                preservation::invalid("original control call lacks its actual interval")
            })?;
            let ports = step
                .inputs()
                .iter()
                .map(|input| input.ty().quantum_basis().and_then(finite_basis))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| {
                    preservation::invalid(
                        "original control call lacks its exact ordered quantum ports",
                    )
                })?;
            let controls = step
                .access_roles()
                .iter()
                .map(|role| *role == QuantumAccess::Ctrl)
                .collect();
            requests.push(ControlRequest {
                root,
                ports,
                controls,
            });
        }
    }
    if requests.is_empty() {
        return Err(preservation::invalid(
            "original control checks were omitted",
        ));
    }
    Ok(requests)
}

pub(super) fn native_error(proposal: &HierarchyProposal, failure: interchange::Error) -> Error {
    let root = &proposal.source.definitions()[proposal.source.root()];
    let module = root
        .path()
        .rsplit_once("::")
        .map_or(root.path(), |(module, _)| module);
    Error::new(failure.code, root.span(), failure.to_string()).in_module(module)
}

#[cfg(all(test, qleisli_native_tests))]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;
    use crate::interchange::hierarchical::Kernel;

    #[test]
    fn same_graph_without_its_native_control_requests_cannot_validate_source() {
        let parsed = ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([(
                "main".into(),
                "pub unitary fn main(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}".into(),
            )]),
        )
        .unwrap();
        let source = parsed
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source.lower_hierarchy_with_controls().unwrap();
        let kernel = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
            source.edition(),
        );
        let ordinary = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let failure = proposal.validate_pure_source_steps(&ordinary).unwrap_err();
        assert_eq!(failure.code(), "preservation");
        assert!(
            failure.message().contains("control obligations"),
            "{failure}"
        );
        let failure = proposal
            .check_pure_with_native(&kernel, proposal.comparison_request())
            .unwrap_err();
        assert_eq!(failure.code(), "contract");
    }
}
