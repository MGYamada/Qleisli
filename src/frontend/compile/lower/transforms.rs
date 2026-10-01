//! Exact, independently extracted expectations for finite static transforms.
use super::super::operations::contract_basis;
use super::*;
use crate::contract::MAX_CONTRACT_BITS;
use crate::contract::exact::{Exact, Matrix};

/// A candidate must be exactly `count` serial copies of the bound body,
/// including controls, scalar phases, axis order and issued evidence identity.
/// Checking copies does not depend on the coefficient growth of the product.
pub(super) fn check_repeated_steps(
    body: &[CircuitStep],
    candidate: &[CircuitStep],
    count: u16,
) -> Result<(), crate::contract::ContractError> {
    let copies = usize::from(count);
    if body.len().checked_mul(copies) != Some(candidate.len()) {
        return Err(crate::contract::ContractError::EquationMismatch);
    }
    if !body.is_empty()
        && candidate
            .chunks_exact(body.len())
            .any(|chunk| chunk != body)
    {
        return Err(crate::contract::ContractError::EquationMismatch);
    }
    Ok(())
}

impl Lowerer<'_, '_> {
    pub(super) fn target_meaning(
        &mut self,
        module: &str,
        name: &Ident,
        basis: &Ty,
    ) -> Result<Option<Matrix>, CompileError> {
        if self.abstract_check || basis.basis_bits().expect("basis") > MAX_CONTRACT_BITS {
            return Ok(None);
        }
        if let Some(op) = self.bindings.get(&name.text) {
            self.compiler.charge(
                module,
                name.span,
                op.meaning.as_ref().map_or(0, |m| m.entries().len()),
            )?;
            return Ok(op.meaning.clone());
        }
        let target = self.compiler.resolve(module, name)?;
        let key = match &target {
            Callee::User(key) => key.clone(),
            // The polymorphic sealed aliases have a different dimension for
            // each exact basis tree. Never reuse a Bit matrix for Unit/product.
            Callee::Sealed(namespace, gate) => (namespace.clone(), format!("{gate}:{basis}")),
        };
        if let Some(matrix) = self.compiler.closed_meanings.get(&key) {
            let cost = matrix.entries().len();
            self.compiler.charge(module, name.span, cost)?;
            return Ok(Some(self.compiler.closed_meanings[&key].clone()));
        }
        let signature = contract_basis(basis);
        let matrix = match target {
            Callee::User(key) => {
                let verified = self.compiler.checked.get(&key).ok_or_else(|| {
                    self.error(
                        module,
                        name.span,
                        ErrorCode::InvalidIr,
                        "static target has not been independently checked",
                    )
                })?;
                crate::contract::function::verified_meaning(
                    verified,
                    &signature,
                    &mut self.compiler.exact_work,
                )
            }
            Callee::Sealed(_, gate) => {
                if matches!(gate.as_str(), "s" | "sdg" | "tdg" | "id" | "phase_eighth") {
                    // Independent expectations use the declared diagonal/scalar
                    // equations, not the candidate lowering or its T expansion.
                    let dimension = 1 << basis.basis_bits().expect("basis");
                    self.compiler
                        .exact_work
                        .charge(dimension * dimension)
                        .map_err(|e| self.compiler.op_error(module, name.span, e.into()))?;
                    let exponent = match gate.as_str() {
                        "s" => 2,
                        "sdg" => 6,
                        "tdg" => 7,
                        "phase_eighth" => 1,
                        _ => 0,
                    };
                    let entries = (0..dimension * dimension)
                        .map(|index| {
                            let row = index / dimension;
                            let column = index % dimension;
                            if row != column {
                                Exact::zero()
                            } else if matches!(gate.as_str(), "s" | "sdg" | "tdg") && row == 0 {
                                Exact::one()
                            } else {
                                Exact::phase(exponent)
                            }
                        })
                        .collect();
                    Matrix::new(dimension, dimension, entries).map_err(Into::into)
                } else {
                    let gate = match gate.as_str() {
                        "h" => SingleGate::H,
                        "x" => SingleGate::X,
                        "z" => SingleGate::Z,
                        "t" => SingleGate::T,
                        _ => unreachable!("static target validated"),
                    };
                    let raw = RawProgram {
                        quantum_inputs: vec![QuantumPort {
                            token: TokenId(0),
                            wires: vec![WireId(0)],
                            shape: BasisShape::BIT,
                        }],
                        classical_inputs: vec![],
                        operations: vec![RawOp::Gate {
                            gate,
                            input: TokenId(0),
                            output: TokenId(1),
                        }],
                        quantum_outputs: vec![TokenId(1)],
                        classical_outputs: vec![],
                        declared_effect: Effect::Unitary,
                    };
                    let verified = crate::verify(raw).expect("fixed sealed primitive");
                    crate::contract::function::verified_meaning(
                        &verified,
                        &signature,
                        &mut self.compiler.exact_work,
                    )
                }
            }
        }
        .map_err(|e| self.compiler.op_error(module, name.span, e))?;
        self.compiler
            .charge(module, name.span, matrix.entries().len().saturating_mul(2))?;
        self.compiler.closed_meanings.insert(key, matrix.clone());
        Ok(Some(matrix))
    }

    pub(super) fn check_transformed(
        &mut self,
        module: &str,
        span: Span,
        basis: &Ty,
        steps: &[CircuitStep],
        expected: Option<&Matrix>,
    ) -> Result<(), CompileError> {
        let Some(expected) = expected else {
            return Ok(());
        };
        let signature = contract_basis(basis);
        let result = super::super::operations::check_steps_meaning(
            &signature,
            steps,
            expected,
            &mut self.compiler.exact_work,
        );
        result.map_err(|e| self.compiler.op_error(module, span, e))
    }

    pub(super) fn qif_meaning(
        &mut self,
        module: &str,
        span: Span,
        zero: Option<Matrix>,
        one: Option<Matrix>,
    ) -> Result<Option<Matrix>, CompileError> {
        let Some((zero, one)) = zero.zip(one) else {
            return Ok(None);
        };
        let d = zero.rows();
        self.compiler
            .exact_work
            .charge(4 * d * d)
            .map_err(|e| self.compiler.op_error(module, span, e.into()))?;
        let mut entries = vec![Exact::zero(); 4 * d * d];
        for (bit, sector) in [&zero, &one].into_iter().enumerate() {
            for y in 0..d {
                for x in 0..d {
                    entries[(2 * y + bit) * 2 * d + 2 * x + bit] =
                        sector.get(y, x).expect("square sector");
                }
            }
        }
        Matrix::new(2 * d, 2 * d, entries)
            .map(Some)
            .map_err(|e| self.compiler.op_error(module, span, e.into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repeated_candidates_reject_changed_phase_control_axis_and_copy_count() {
        let body = vec![CircuitStep {
            controls: vec![BitControl {
                index: 0,
                when_one: true,
            }],
            action: CircuitAction::Monomial {
                indices: vec![1],
                permutation: vec![0, 1],
                phases: vec![0, 1],
            },
        }];
        let candidate: Vec<_> = (0..3).flat_map(|_| body.iter().cloned()).collect();
        assert!(check_repeated_steps(&body, &candidate, 3).is_ok());
        assert!(check_repeated_steps(&body, &candidate, 2).is_err());
        for fault in 0..3 {
            let mut bad = candidate.clone();
            match fault {
                0 => bad[1].controls[0].when_one = false,
                1 => {
                    if let CircuitAction::Monomial { phases, .. } = &mut bad[1].action {
                        phases[1] = 7;
                    }
                }
                _ => {
                    if let CircuitAction::Monomial { indices, .. } = &mut bad[1].action {
                        indices[0] = 2;
                    }
                }
            }
            assert!(check_repeated_steps(&body, &bad, 3).is_err());
        }
        assert!(check_repeated_steps(&body, &[], 0).is_ok());
        assert!(check_repeated_steps(&[], &[], u16::MAX).is_ok());
        assert!(check_repeated_steps(&[], &candidate, 0).is_err());
    }
}
