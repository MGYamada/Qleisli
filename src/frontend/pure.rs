//! Shared proposals for finite two-port bodies. Only native decisions accept.
use crate::contract::{
    BasisType, ContractError,
    exact::{Budget, Matrix},
};
use crate::interchange::{RootInterface, Version, native, pure_leaf};
use crate::ir::*;

pub(super) fn combine(
    left: &pure_leaf::CheckedPureLeaf,
    right: &pure_leaf::CheckedPureLeaf,
    tensor: bool,
    budget: &mut Budget,
) -> Result<RawProgram, ContractError> {
    let a = left.boundary();
    let b = right.boundary();
    if !tensor && a.codomain() != b.domain() {
        return Err(ContractError::Type(
            "composition requires identical intermediate basis trees",
        ));
    }
    let mut state = super::raw_state::RawState::<()>::new();
    let bits = a.domain().bits()? + if tensor { b.domain().bits()? } else { 0 };
    let input = QuantumPort {
        token: state.token(),
        wires: (0..bits).map(|_| state.wire()).collect(),
        shape: BasisShape { bits: bits as u8 },
    };
    let output = if tensor {
        let cut = a.domain().bits()?;
        let low = QuantumPort {
            token: state.token(),
            wires: input.wires[..cut].to_vec(),
            shape: a.input().shape,
        };
        let high = QuantumPort {
            token: state.token(),
            wires: input.wires[cut..].to_vec(),
            shape: b.input().shape,
        };
        state.operations.push(RawOp::Split {
            input: input.token,
            left: low.token,
            right: high.token,
            left_bits: cut as u8,
        });
        let low = super::raw_splice::append(&mut state, left.program(), &low, budget)?;
        let high = super::raw_splice::append(&mut state, right.program(), &high, budget)?;
        let token = state.token();
        state.operations.push(RawOp::Join {
            left: low.token,
            right: high.token,
            output: token,
        });
        token
    } else {
        let middle = super::raw_splice::append(&mut state, left.program(), &input, budget)?;
        super::raw_splice::append(&mut state, right.program(), &middle, budget)?.token
    };
    Ok(RawProgram {
        quantum_inputs: vec![input],
        classical_inputs: vec![],
        operations: state.operations,
        quantum_outputs: vec![output],
        classical_outputs: vec![],
        declared_effect: left
            .program()
            .raw()
            .declared_effect
            .max(right.program().raw().declared_effect),
    })
}

pub(super) fn check(
    kernel: &native::Kernel,
    raw: &RawProgram,
    domain: &BasisType,
    codomain: &BasisType,
    expected: Option<&Matrix>,
    budget: &mut Budget,
) -> Result<pure_leaf::CheckedPureLeaf, ContractError> {
    let error = |e: crate::interchange::Error| ContractError::InvalidCircuit(e.to_string());
    let proposal = native::Proposal::from_raw(
        raw,
        Some(&RootInterface {
            input: domain.clone(),
            output: codomain.clone(),
        }),
        Version::V2,
        None,
    )
    .map_err(error)?;
    budget.charge(proposal.artifact().len())?;
    let accepted = kernel.accept(&proposal).map_err(error)?;
    budget.charge(accepted.native_exact_work())?;
    let ([input], [output]) = (
        accepted.raw().quantum_inputs.as_slice(),
        accepted.output_ports(),
    ) else {
        return Err(ContractError::Type(
            "pure operation requires one quantum input and output",
        ));
    };
    let boundary = pure_leaf::PureBoundary::new(
        domain.clone(),
        codomain.clone(),
        input.clone(),
        output.clone(),
    )
    .map_err(error)?;
    let proposed;
    let expected = match expected {
        Some(value) => value,
        None => {
            proposed = crate::contract::function::propose_pure_meaning(
                &accepted, domain, codomain, budget,
            )?;
            &proposed
        }
    };
    pure_leaf::check_with_kernel(kernel, proposal.artifact(), &boundary, expected, budget)
        .map_err(error)
}
