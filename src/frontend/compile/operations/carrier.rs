//! Logical operator proposals for exact nominal ports.
//! Native v5 checks the source, provider, codes, and actual application.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

impl Compiler<'_> {
    pub(super) fn retain_carrier_meaning(
        &mut self,
        key: Key,
        basis: Ty,
        codomain: Ty,
        matrix: Matrix,
        references: Vec<Key>,
    ) {
        self.meanings.insert(
            key,
            DeclaredMeaning {
                basis,
                codomain,
                target: None,
                raw: None,
                references,
                matrix,
                pure: None,
            },
        );
    }

    pub(super) fn carrier_table_action(
        &mut self,
        module: &str,
        span: Span,
        basis: &Ty,
        permutation: bool,
        table: &[u16],
    ) -> Result<Matrix, CompileError> {
        let (_, codes) = self.basis_codes(module, span, basis)?;
        let dimension = codes.len();
        if table.len() != dimension {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "Meaning table differs from its exact logical carrier",
            ));
        }
        self.exact_work
            .charge(dimension * dimension + dimension)
            .map_err(|e| self.op_error(module, span, e.into()))?;
        let mut entries = vec![Exact::zero(); dimension * dimension];
        let mut seen = BTreeSet::new();
        for (input, &label) in table.iter().enumerate() {
            if permutation {
                let row = codes.binary_search(&usize::from(label)).map_err(|_| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Contract,
                        "Meaning maps a canonical input to a padding code",
                    )
                })?;
                if !seen.insert(row) {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Contract,
                        "Meaning is not a permutation of the exact logical carrier",
                    ));
                }
                entries[row * dimension + input] = Exact::one();
            } else {
                if label > 7 {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Contract,
                        "phase label is outside zeta_8",
                    ));
                }
                entries[input * dimension + input] = Exact::phase(i32::from(label));
            }
        }
        Matrix::new(dimension, dimension, entries)
            .map_err(|e| self.op_error(module, span, e.into()))
    }

    fn logical_coordinates(
        &mut self,
        module: &str,
        span: Span,
        physical: &Matrix,
        input: &[usize],
        output: &[usize],
    ) -> Result<Matrix, CompileError> {
        self.exact_work
            .charge(physical.rows() * input.len() + input.len() * output.len())
            .map_err(|e| self.op_error(module, span, e.into()))?;
        for row in 0..physical.rows() {
            if output.binary_search(&row).is_err()
                && input
                    .iter()
                    .any(|&column| physical.get(row, column) != Some(Exact::zero()))
            {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Contract,
                    "operator maps an original canonical input outside the output code",
                ));
            }
        }
        let mut entries = Vec::with_capacity(input.len() * output.len());
        for &row in output {
            for &column in input {
                let value = physical.get(row, column).ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Contract,
                        "operator coordinates differ from the original code",
                    )
                })?;
                entries.push(value);
            }
        }
        Matrix::new(output.len(), input.len(), entries)
            .map_err(|e| self.op_error(module, span, e.into()))
    }

    pub(super) fn carrier_program_action(
        &mut self,
        module: &str,
        span: Span,
        basis: &Ty,
        codomain: &Ty,
        program: &AcceptedProgram,
    ) -> Result<Matrix, CompileError> {
        let (input_bits, input) = self.basis_codes(module, span, basis)?;
        let (output_bits, output) = self.basis_codes(module, span, codomain)?;
        let physical = crate::contract::function::propose_pure_coordinates(
            program,
            input_bits,
            output_bits,
            &mut self.exact_work,
        )
        .map_err(|e| self.op_error(module, span, e))?;
        self.logical_coordinates(module, span, &physical, &input, &output)
    }

    pub(super) fn carrier_circuit_action(
        &mut self,
        module: &str,
        span: Span,
        basis: &Ty,
        steps: Vec<CircuitStep>,
    ) -> Result<Matrix, CompileError> {
        let (width, codes) = self.basis_codes(module, span, basis)?;
        let physical = Circuit::for_coordinates(width, steps)
            .and_then(|c| c.matrix(&mut self.exact_work))
            .map_err(|e| self.op_error(module, span, e))?;
        self.logical_coordinates(module, span, &physical, &codes, &codes)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn carrier_provider_program(
        &mut self,
        module: &str,
        span: Span,
        key: Key,
        meaning: Option<Key>,
        effect: Effect,
        basis: Ty,
        codomain: Ty,
        program: &AcceptedProgram,
    ) -> Result<Operation, CompileError> {
        let Some(meaning) = meaning else {
            return Err(self.error(
                module,
                span,
                ErrorCode::Unsupported,
                "typed provider requires an original checked Meaning occurrence",
            ));
        };
        if effect > Effect::Isometry {
            return Err(self.error(
                module,
                span,
                ErrorCode::Effect,
                "typed Meaning provider requires an available pure effect",
            ));
        }
        let invertible = effect == Effect::Unitary && basis == codomain;
        let (steps, matrix) = if invertible {
            let steps = circuit::flatten(self, module, span, program)?;
            self.charge(module, span, total_size(steps.iter().map(circuit::size)))?;
            let matrix = self.carrier_circuit_action(module, span, &basis, steps.clone())?;
            (Some(steps), matrix)
        } else {
            let matrix = self.carrier_program_action(module, span, &basis, &codomain, program)?;
            (None, matrix)
        };
        let source_origin = self.provider_origin(key, Some(meaning), program, module, span)?;
        let operation = Operation {
            basis,
            codomain,
            effect,
            meaning: Some(matrix),
            access: [true, invertible, invertible],
            node: Arc::new(Node::Carrier(steps)),
            source_origin: Some(source_origin),
            source_formal: None,
            depth: 1,
            nodes: 1,
        };
        self.validate_operation_meaning(&operation, meaning, module, span)?;
        Ok(operation)
    }
}
