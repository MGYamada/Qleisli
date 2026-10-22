//! Explicit source-to-carrier proposals through the shared Builder and Raw emitter.
//! No ordinary execution handle or AST preservation theorem is produced here.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::contract::exact::Matrix;
use crate::frontend::specialize::Instantiation;
use crate::interchange::carrier::{self as transport, Interface, Owner, Request};

/// A fresh native carrier equation and independent replay of the same retained
/// source steps. Its private source and decoded root cannot become an ordinary
/// accepted program. This grants no runtime, inverse or control capability.
///
/// ```compile_fail
/// use qleisli::frontend::compile::CheckedSourceCarrier;
/// use qleisli::interchange::native::AcceptedProgram;
/// fn bypass(checked: CheckedSourceCarrier) -> AcceptedProgram { checked.into() }
/// ```
#[derive(Debug)]
pub struct CheckedSourceCarrier {
    source: ElaboratedProgram,
    checked: native::CarrierChecked,
}

impl CheckedSourceCarrier {
    pub fn artifact(&self) -> &[u8] {
        self.checked.artifact()
    }
    pub fn request_bytes(&self) -> &[u8] {
        self.checked.request_bytes()
    }
    pub fn request(&self) -> &Request {
        self.checked.request()
    }
    pub fn native(&self) -> &native::NativeChecked {
        self.checked.native()
    }
    pub fn entry(&self) -> &str {
        self.source.instantiation().entry()
    }
    /// Native code/body equations and retained-step replay do not prove the
    /// original function AST elaborates to these steps.
    pub fn source_meaning_verified(&self) -> bool {
        false
    }
}

impl Instantiation {
    /// Elaborate this exact original source using the common judgment and full
    /// source Builder, then check its emitted body against an explicitly supplied
    /// independent exact logical matrix. The matrix is never inferred from the
    /// emitted physical matrix. Only the bounded pure carrier profile is enabled;
    /// ordinary ADT execution remains unavailable.
    pub fn check_carrier(
        &self,
        kernel: &native::Kernel,
        logical: &Matrix,
        budget: &mut Budget,
    ) -> Result<CheckedSourceCarrier> {
        if budget.remaining() > DEFAULT_EXACT_WORK {
            return Err(Error::new(
                "limit",
                Span::default(),
                "carrier budget exceeds the shared exact-work ceiling",
            ));
        }
        let (source, work) = super::super::elaborate::carrier_preparation(self)?;
        source.require_edition(kernel.edition())?;
        let span = source.definitions()[source.root()].span();
        charge(budget, span, work)?;
        source.require_function_contracts()?;
        source.require_control_evidence()?;
        if source.has_operation_meanings() {
            return Err(Error::new(
                "unsupported",
                span,
                "source carrier route requires independently connected original operation Meanings",
            ));
        }
        let proposal = lower_inner_profile(
            &source,
            source.root(),
            None,
            None,
            None,
            Some((logical, budget)),
        )?;
        let request = proposal
            .proposal
            .request()
            .ok_or_else(|| invalid(span, "carrier proposal omits its original typed request"))?;
        charge(
            budget,
            span,
            proposal.payload().len().saturating_add(request.len()),
        )?;
        let checked = kernel
            .check_carrier(proposal.payload(), request)
            .map_err(|e| Error::new(e.code, span, e.to_string()))?;
        charge(budget, span, checked.native().exact_work())?;
        if checked.artifact() != proposal.payload() || checked.request_bytes() != request {
            return Err(invalid(
                span,
                "native carrier decision differs from the immutable source artifact or request",
            ));
        }
        preservation::validate_subject_with_meanings(
            &source,
            source.root(),
            None,
            checked.raw(),
            Some(kernel),
            budget,
            &[],
        )?;
        Ok(CheckedSourceCarrier { source, checked })
    }
}

fn charge(budget: &mut Budget, span: Span, cells: usize) -> Result<()> {
    budget
        .charge(cells)
        .map_err(|e| Error::new("limit", span, e.to_string()))
}

fn bases<'a>(
    ty: &'a SourceType,
    out: &mut Vec<&'a SourceType>,
    span: Span,
    budget: &mut Budget,
) -> Result<()> {
    charge(budget, span, 1)?;
    match &ty.kind {
        Kind::Unit => Ok(()),
        Kind::Q(basis) => {
            out.push(basis);
            Ok(())
        }
        Kind::Tuple(fields) => {
            for field in fields {
                bases(field, out, span, budget)?;
            }
            Ok(())
        }
        _ => Err(Error::new(
            "unsupported",
            span,
            "source carrier root requires quantum owners and ordinary Unit products",
        )),
    }
}

fn owners(
    types: &[&SourceType],
    ports: &[QuantumPort],
    span: Span,
    budget: &mut Budget,
) -> Result<Vec<Owner>> {
    if types.len() != ports.len() {
        return Err(invalid(
            span,
            "source carrier owner arity differs from emitted ports",
        ));
    }
    let mut owners = Vec::new();
    for (ty, port) in types.iter().zip(ports) {
        charge(budget, span, port.wires.len().saturating_add(1))?;
        let basis = super::super::basis_binding::carrier_description_budgeted(ty, &mut |at, n| {
            charge(budget, at, n)
        })?;
        owners.push(Owner {
            port: port.clone(),
            basis,
        });
    }
    Ok(owners)
}

// Every attached row is exact original source, covered by a retained nominal
// origin. The complete source collection remains inside the sealed holder.
// Import/helper-only modules cannot be smuggled in as unclaimed source rows.
fn sources(
    source: &ElaboratedProgram,
    interface: &Interface,
    span: Span,
    budget: &mut Budget,
) -> Result<Vec<(String, String)>> {
    let mut rows = BTreeMap::<String, String>::new();
    for owner in interface.inputs.iter().chain(&interface.outputs) {
        for atom in &owner.basis {
            charge(budget, span, 1)?;
            let (transport::Atom::Enum(origin, _) | transport::Atom::Record(origin, _)) = atom
            else {
                continue;
            };
            let original = source
                .instantiation()
                .program
                .sources
                .get(&origin.module)
                .ok_or_else(|| {
                    invalid(
                        span,
                        "carrier nominal source is absent from the retained collection",
                    )
                })?;
            if original.text() != origin.source {
                return Err(invalid(
                    span,
                    "carrier nominal source differs from original bytes",
                ));
            }
            if let Some(previous) = rows.get(&origin.module) {
                if previous != &origin.source {
                    return Err(invalid(
                        span,
                        "carrier nominal origins disagree on original source",
                    ));
                }
            } else {
                charge(
                    budget,
                    span,
                    origin
                        .module
                        .len()
                        .saturating_add(origin.source.len())
                        .saturating_add(2),
                )?;
                rows.insert(origin.module.clone(), origin.source.clone());
            }
        }
    }
    for definition in source.definitions() {
        charge(budget, span, 1)?;
        let module = definition
            .path()
            .rsplit_once("::")
            .map_or(definition.path(), |(module, _)| module);
        if !rows.contains_key(module) {
            return Err(Error::new("unsupported", definition.span(), "source carrier requires every selected body module to have an exact nominal origin; helper/import-only rows remain unsupported").in_module(module));
        }
    }
    Ok(rows.into_iter().collect())
}

pub(super) fn proposal(
    source: &ElaboratedProgram,
    raw: &RawProgram,
    output_ports: &[QuantumPort],
    logical: &Matrix,
    budget: &mut Budget,
) -> Result<native::Proposal> {
    let root = &source.definitions()[source.root()];
    let span = root.span();
    let public_effect = source.instantiation().program.checked.effects[&root.original]
        .public_effect()
        .ok_or_else(|| {
            Error::new(
                "unsupported",
                span,
                "source carrier root requires an explicit public quantum effect",
            )
        })?;
    if public_effect > Effect::Isometry
        || raw.declared_effect > Effect::Isometry
        || !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
    {
        return Err(Error::new(
            "unsupported",
            span,
            "source carrier requires a pure public contract and actual pure body",
        ));
    }
    let mut inputs = Vec::new();
    for input in root.inputs() {
        bases(input.ty(), &mut inputs, span, budget)?;
    }
    let mut outputs = Vec::new();
    bases(root.output().ty(), &mut outputs, span, budget)?;
    let interface = Interface {
        inputs: owners(&inputs, &raw.quantum_inputs, span, budget)?,
        outputs: owners(&outputs, output_ports, span, budget)?,
        public_effect,
    };
    let rows = sources(source, &interface, span, budget)?;
    // Charge identifier clones and both JSON object/string copies before
    // allocation. Eight cells per source byte also covers worst-case JSON
    // escaping, while shared Origin Arcs themselves need no source clone.
    let strings = |n: usize| n.saturating_mul(8);
    let mut interface_cells = 128usize;
    for owner in interface.inputs.iter().chain(&interface.outputs) {
        interface_cells = interface_cells
            .saturating_add(128)
            .saturating_add(owner.port.wires.len().saturating_mul(16));
        for atom in &owner.basis {
            interface_cells = interface_cells.saturating_add(128);
            if let transport::Atom::Enum(origin, names) | transport::Atom::Record(origin, names) =
                atom
            {
                interface_cells = interface_cells.saturating_add(strings(
                    origin
                        .module
                        .len()
                        .saturating_add(origin.declaration.len())
                        .saturating_add(origin.source.len()),
                ));
                for name in names {
                    interface_cells =
                        interface_cells.saturating_add(strings(name.len()).saturating_add(16));
                }
            }
        }
    }
    // Every exact scalar uses four bounded i128 coefficients and one bounded
    // denominator. This also covers their intermediate JSON containers.
    let request_cells = interface_cells
        .saturating_mul(2)
        .saturating_add(logical.entries().len().saturating_mul(512))
        .saturating_add(256);
    let row_cells = rows.iter().fold(0usize, |n, (path, text)| {
        n.saturating_add(strings(path.len().saturating_add(text.len())))
            .saturating_add(64)
    });
    charge(budget, span, request_cells.saturating_add(row_cells))?;
    let request = Request {
        attached: interface.clone(),
        required: interface,
        logical: logical.clone(),
    }
    .encode()
    .map_err(|e| Error::new("transport", span, e.to_string()))?;
    charge(budget, span, request.len())?;
    native::Proposal::from_raw_with_sources(raw, None, Version::V2, Some(&request), &rows)
        .map_err(|e| Error::new("transport", span, e.to_string()))
}

#[cfg(test)]
mod tests;
