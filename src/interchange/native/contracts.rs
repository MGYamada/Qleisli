//! Untrusted serialization of encoded equations and complete finite-leaf requests.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::exact::Matrix;
use crate::contract::function::{RetainedIdentity, validate_identity};
use crate::contract::instrument::{ResultAtom, Signature};
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
    /// Serialize the reviewed instrument request and obtain a fresh decision.
    /// Both signatures and the expected original artifact remain request data,
    /// never a producer-supplied matrix or a reusable acceptance receipt.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_instrument(
        &self,
        actual: &[u8],
        actual_signature: &Signature,
        expected: &[u8],
        expected_signature: &Signature,
        identity: &RetainedIdentity,
        budget: &mut crate::contract::exact::Budget,
    ) -> Result<NativeChecked> {
        let map = super::super::contract_error;
        actual_signature.validate(budget).map_err(map)?;
        expected_signature.validate(budget).map_err(map)?;
        validate_identity(identity, budget).map_err(map)?;
        if expected.is_empty() || expected.len() > 16 * 1024 * 1024 {
            return Err(map(crate::contract::ContractError::Limit(
                "expected instrument artifact exceeds 16 MiB",
            )));
        }
        let expected = std::str::from_utf8(expected).map_err(|_| {
            map(crate::contract::ContractError::Type(
                "expected instrument artifact must be UTF-8",
            ))
        })?;
        let (implementation, specification, sources) = identity.parts();
        let storage = sources
            .iter()
            .try_fold(
                expected.len() + implementation.len() + specification.len(),
                |bytes, (path, source)| bytes.checked_add(path.len())?.checked_add(source.len()),
            )
            .ok_or_else(|| {
                map(crate::contract::ContractError::Limit(
                    "instrument request size overflow",
                ))
            })?;
        budget
            .charge(storage)
            .map_err(crate::contract::ContractError::from)
            .map_err(map)?;
        let mut encoder = Encoder::new(Version::V2);
        let request = json::encode(&Value::object([
            ("format", Value::String("qleisli.native-contract".into())),
            ("version", Value::Number(1)),
            ("kind", Value::String("instrument".into())),
            (
                "actual_signature",
                instrument_signature(actual_signature, &mut encoder)?,
            ),
            (
                "expected_signature",
                instrument_signature(expected_signature, &mut encoder)?,
            ),
            (
                "identity",
                Value::object([
                    ("implementation", Value::String(implementation.into())),
                    ("specification", Value::String(specification.into())),
                    (
                        "sources",
                        Value::Array(
                            sources
                                .iter()
                                .map(|(path, text)| {
                                    Value::object([
                                        ("path", Value::String(path.clone())),
                                        ("text", Value::String(text.clone())),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ]),
            ),
            ("expected_artifact", Value::String(expected.into())),
        ]))?;
        let accepted = self.inspect_mode(actual, Some(&request), "--qirf-contract")?;
        budget
            .charge(accepted.exact_work())
            .map_err(crate::contract::ContractError::from)
            .map_err(map)?;
        Ok(accepted)
    }

    /// Independently inspect the actual call fragment selected by source replay.
    /// No producer matrix or success receipt participates in this request.
    pub(crate) fn check_control_owners(
        &self,
        raw: &RawProgram,
        signatures: &[BasisType],
        axes: &[usize],
        budget: &mut crate::contract::exact::Budget,
    ) -> Result<NativeChecked> {
        let proposal = Proposal::from_raw(raw, None, Version::V2, None)?;
        let mut encoder = Encoder::new(Version::V2);
        let request = json::encode(&Value::object([
            ("format", Value::String("qleisli.native-contract".into())),
            ("version", Value::Number(1)),
            ("kind", Value::String("control-owners".into())),
            (
                "signatures",
                Value::Array(
                    signatures
                        .iter()
                        .map(|signature| signature.write(&mut encoder))
                        .collect::<Result<_>>()?,
                ),
            ),
            (
                "axes",
                Value::Array(
                    axes.iter()
                        .map(|axis| Value::Number(*axis as u64))
                        .collect(),
                ),
            ),
        ]))?;
        let accepted = self.inspect_mode(proposal.artifact(), Some(&request), "--qirf-contract")?;
        budget
            .charge(accepted.exact_work())
            .map_err(crate::contract::ContractError::from)
            .map_err(super::super::contract_error)?;
        Ok(accepted)
    }

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

// Called only after bounded prefix/basis validation. The JSON uses the exact
// nested protocol representation; the older flattened contract basis differs.
fn instrument_signature(signature: &Signature, encoder: &mut Encoder) -> Result<Value> {
    fn result(atoms: &[ResultAtom], cursor: &mut usize, encoder: &mut Encoder) -> Result<Value> {
        let atom = &atoms[*cursor];
        *cursor += 1;
        let tagged = |tag: &str| ("tag", Value::String(tag.into()));
        Ok(match atom {
            ResultAtom::Unit => Value::object([tagged("unit")]),
            ResultAtom::Bit => Value::object([tagged("bit")]),
            ResultAtom::Bits(width) => {
                Value::object([tagged("bits"), ("width", Value::Number(u64::from(*width)))])
            }
            ResultAtom::Quantum(basis) => {
                Value::object([tagged("quantum"), ("basis", basis.write(encoder)?)])
            }
            ResultAtom::Pair => Value::object([
                tagged("pair"),
                ("left", result(atoms, cursor, encoder)?),
                ("right", result(atoms, cursor, encoder)?),
            ]),
            ResultAtom::Tuple(count) => Value::object([
                tagged("tuple"),
                (
                    "fields",
                    Value::Array(
                        (0..*count)
                            .map(|_| result(atoms, cursor, encoder))
                            .collect::<Result<_>>()?,
                    ),
                ),
            ]),
        })
    }
    Ok(Value::object([
        ("input", signature.input.write(encoder)?),
        ("result", result(&signature.result, &mut 0, encoder)?),
    ]))
}
