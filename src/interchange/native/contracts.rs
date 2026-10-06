//! Untrusted serialization of encoded equations and complete finite-leaf requests.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::exact::Matrix;
use crate::contract::{BasisType, Circuit, Contract, Encoding};
use crate::interchange::{
    codec::Codec,
    json::{self, Value},
};
use crate::ir::*;

fn atoms(ty: &BasisType, out: &mut Vec<Value>) {
    match ty {
        BasisType::Unit => out.push(Value::String("unit".into())),
        BasisType::Bit => out.push(Value::String("bit".into())),
        BasisType::Bits(width) => out.push(Value::String(format!("bits:{width}"))),
        BasisType::Pair(a, b) => {
            out.push(Value::String("pair".into()));
            atoms(a, out);
            atoms(b, out);
        }
        BasisType::Tuple(fields) => {
            out.push(Value::String(format!("tuple:{}", fields.len())));
            for field in fields {
                atoms(field, out);
            }
        }
    }
}
fn basis(ty: &BasisType) -> Value {
    let mut out = vec![];
    atoms(ty, &mut out);
    Value::Array(out)
}
fn matrix(value: &Matrix) -> Result<Value> {
    json::parse(&crate::interchange::finite_matrix::encode(value)?)
}
fn encoding(value: &Encoding) -> Result<Value> {
    Ok(Value::object([
        ("logical", basis(value.logical())),
        ("physical", basis(value.physical())),
        ("map", matrix(value.map())?),
    ]))
}
fn contract(value: &Contract) -> Result<Value> {
    Ok(Value::object([
        ("input", encoding(value.input())?),
        ("output", encoding(value.output())?),
        ("logical", matrix(value.logical())?),
    ]))
}

impl Kernel {
    pub(crate) fn check_encoded(
        &self,
        circuit: &Circuit,
        required: &Contract,
    ) -> Result<NativeChecked> {
        let bits = circuit
            .basis()
            .bits()
            .map_err(super::super::contract_error)?;
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: (0..bits as u32).map(WireId).collect(),
                shape: BasisShape { bits: bits as u8 },
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: circuit.steps().to_vec(),
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let interface = RootInterface {
            input: circuit.basis().clone(),
            output: circuit.basis().clone(),
        };
        let proposal = Proposal::from_raw(&raw, Some(&interface), Version::V2, None)?;
        let request = json::encode(&Value::object([
            ("format", Value::String("qleisli.native-contract".into())),
            ("version", Value::Number(1)),
            ("kind", Value::String("encoded".into())),
            ("contract", contract(required)?),
        ]))?;
        self.inspect_mode(proposal.artifact(), Some(&request), "--qirf-contract")
    }

    pub(crate) fn check_leaf(
        &self,
        payload: &[u8],
        boundary: &crate::interchange::finite_leaf::UnitaryBoundary,
        required: &Matrix,
    ) -> Result<AcceptedProgram> {
        let mut encoder = Encoder::new(Version::V2);
        let request = json::encode(&Value::object([
            ("format", Value::String("qleisli.native-contract".into())),
            ("version", Value::Number(1)),
            ("kind", Value::String("leaf".into())),
            ("signature", boundary.signature().write(&mut encoder)?),
            ("input", boundary.input().write(&mut encoder)?),
            ("output", boundary.output().write(&mut encoder)?),
            ("matrix", matrix(required)?),
        ]))?;
        Self::decode_checked(self.inspect_mode(payload, Some(&request), "--qirf-contract")?)
            .map(Checked::into_program)
    }
}
