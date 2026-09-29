//! Exact, independently extracted expectations for finite static transforms.
use super::super::operations::contract_basis;
use super::*;
use crate::contract::MAX_CONTRACT_BITS;
use crate::contract::exact::{Exact, Matrix};

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
            Callee::Sealed(namespace, gate) => (namespace.clone(), gate.clone()),
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
