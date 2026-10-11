//! Private original-artifact instrument equations, separate from pure Meaning.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use std::fmt;
use std::sync::Arc;

use super::exact::Budget;
use super::function::RetainedIdentity;
use super::{BasisType, ContractError, MAX_CONTRACT_BITS};
use crate::interchange::Version;
use crate::interchange::native::{AcceptedProgram, Kernel, NativeChecked, Proposal};
use crate::ir::RawProgram;

const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 64;

/// Prefix form retains the complete result tree without recursive host drops.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum ResultAtom {
    Unit,
    Bit,
    Bits(u32),
    Quantum(BasisType),
    Pair,
    Tuple(usize),
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Signature {
    pub(crate) input: BasisType,
    pub(crate) result: Vec<ResultAtom>,
}

impl Signature {
    pub(crate) fn validate(&self, budget: &mut Budget) -> Result<(), ContractError> {
        basis_width(&self.input, budget)?;
        if self.result.is_empty() || self.result.len() > MAX_NODES {
            return Err(ContractError::Limit("instrument result exceeds 4096 nodes"));
        }
        let mut pending = vec![1usize];
        let mut quantum_width = 0usize;
        for (index, atom) in self.result.iter().enumerate() {
            budget.charge(1)?;
            let depth = pending
                .pop()
                .ok_or(ContractError::Type("instrument result has trailing nodes"))?;
            if depth > MAX_DEPTH {
                return Err(ContractError::Limit("instrument result exceeds depth 64"));
            }
            let children = match atom {
                ResultAtom::Pair => 2,
                ResultAtom::Tuple(count) if (3..=MAX_NODES).contains(count) => *count,
                ResultAtom::Tuple(_) => {
                    return Err(ContractError::Type(
                        "instrument tuples require at least three fields",
                    ));
                }
                ResultAtom::Quantum(basis) => {
                    quantum_width = quantum_width
                        .checked_add(basis_width(basis, budget)?)
                        .ok_or(ContractError::Limit("instrument quantum width overflow"))?;
                    if quantum_width > MAX_CONTRACT_BITS {
                        return Err(ContractError::Limit(
                            "instrument output exceeds six quantum bits",
                        ));
                    }
                    0
                }
                ResultAtom::Unit | ResultAtom::Bit | ResultAtom::Bits(_) => 0,
            };
            // Bound the frontier before allocating it, including malformed
            // producer arities. Every pending slot needs a remaining atom.
            if children + pending.len() > self.result.len() - index - 1 {
                return Err(ContractError::Type("instrument result is incomplete"));
            }
            budget.charge(children)?;
            pending.extend(std::iter::repeat_n(depth + 1, children));
        }
        if !pending.is_empty() {
            return Err(ContractError::Type("instrument result is incomplete"));
        }
        Ok(())
    }
}

fn basis_width(basis: &BasisType, budget: &mut Budget) -> Result<usize, ContractError> {
    let mut pending = vec![(basis, 1)];
    let mut visited = 0usize;
    let mut width = 0usize;
    while let Some((basis, depth)) = pending.pop() {
        budget.charge(1)?;
        visited += 1;
        if visited > MAX_NODES || depth > MAX_DEPTH {
            return Err(ContractError::Limit(
                "instrument basis exceeds 4096 nodes or depth 64",
            ));
        }
        let extra = match basis {
            BasisType::Unit => 0,
            BasisType::Bit => 1,
            BasisType::Bits(n) => *n as usize,
            BasisType::Pair(a, b) => {
                if visited + pending.len() + 2 > MAX_NODES {
                    return Err(ContractError::Limit("instrument basis exceeds 4096 nodes"));
                }
                budget.charge(2)?;
                pending.extend([(b.as_ref(), depth + 1), (a.as_ref(), depth + 1)]);
                0
            }
            BasisType::Tuple(fields) => {
                if fields.len() < 3 {
                    return Err(ContractError::Type(
                        "instrument basis tuples require at least three fields",
                    ));
                }
                if fields.len() > MAX_NODES - visited - pending.len() {
                    return Err(ContractError::Limit("instrument basis exceeds 4096 nodes"));
                }
                budget.charge(fields.len())?;
                pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                0
            }
        };
        width = width
            .checked_add(extra)
            .ok_or(ContractError::Limit("instrument basis width overflow"))?;
        if width > MAX_CONTRACT_BITS {
            return Err(ContractError::Limit(
                "instrument basis exceeds six quantum bits",
            ));
        }
    }
    Ok(width)
}

/// Issued only after the selected native checker freshly compares both
/// original graphs. This is neither a first-class operation nor a root request.
pub(crate) struct InstrumentEvidence {
    signature: Signature,
    expected_signature: Signature,
    implementation: AcceptedProgram,
    specification: AcceptedProgram,
    identity: RetainedIdentity,
    native: NativeChecked,
}

impl fmt::Debug for InstrumentEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InstrumentEvidence")
            .field("signature", &self.signature)
            .field("expected_signature", &self.expected_signature)
            .field("identity", &self.identity.parts())
            .field("actual_bytes", &self.native.artifact().len())
            .field(
                "implementation_bytes",
                &self.implementation.artifact().len(),
            )
            .field("expected_bytes", &self.specification.artifact().len())
            .finish()
    }
}

impl InstrumentEvidence {
    pub(crate) fn check(
        kernel: &Kernel,
        signature: Signature,
        expected_signature: Signature,
        implementation: &AcceptedProgram,
        specification: &AcceptedProgram,
        identity: RetainedIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        signature.validate(budget)?;
        let native = kernel
            .check_instrument(
                implementation.artifact(),
                &signature,
                specification.artifact(),
                &expected_signature,
                &identity,
                budget,
            )
            .map_err(native_error)?;
        // Raw bodies, native bytes and nested source sidecars are immutable
        // shared snapshots; only output-port metadata is copied by this clone.
        for program in [implementation, specification] {
            budget.charge(
                program
                    .output_ports()
                    .iter()
                    .map(|port| port.wires.len() + 3)
                    .sum(),
            )?;
        }
        Ok(Self {
            signature,
            expected_signature,
            implementation: implementation.clone(),
            specification: specification.clone(),
            identity,
            native,
        })
    }

    /// Reconstruct the actual emitted call again. Reusing the frozen selected
    /// reference never reuses an earlier acceptance decision for this call.
    pub(crate) fn check_call(
        self: &Arc<Self>,
        kernel: &Kernel,
        signature: &Signature,
        actual: &RawProgram,
        source: (String, usize, usize),
        budget: &mut Budget,
    ) -> Result<InstrumentCall, ContractError> {
        budget.charge(source.0.len() + 3)?;
        let (_, _, originals) = self.identity.parts();
        budget.charge(originals.iter().map(|(name, _)| name.len() + 1).sum())?;
        let text = originals
            .iter()
            .find(|(name, _)| name == &source.0)
            .map(|(_, text)| text)
            .ok_or(ContractError::EvidenceMismatch)?;
        if source.1 > source.2
            || source.2 > text.len()
            || !text.is_char_boundary(source.1)
            || !text.is_char_boundary(source.2)
        {
            return Err(ContractError::EvidenceMismatch);
        }
        let actual = Proposal::from_raw(actual, None, Version::V2, None).map_err(native_error)?;
        let native = kernel
            .check_instrument(
                actual.artifact(),
                signature,
                self.specification.artifact(),
                &self.expected_signature,
                &self.identity,
                budget,
            )
            .map_err(native_error)?;
        Ok(InstrumentCall {
            pair: Arc::clone(self),
            native,
            source,
        })
    }
}

/// Retains the checked pair, exact call ports/instructions/results and original
/// source position. The enclosing root still needs its own ordinary decision.
pub(crate) struct InstrumentCall {
    pair: Arc<InstrumentEvidence>,
    native: NativeChecked,
    source: (String, usize, usize),
}
impl fmt::Debug for InstrumentCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InstrumentCall")
            .field("source", &self.source)
            .field("pair", &self.pair)
            .field("actual_bytes", &self.native.artifact().len())
            .finish()
    }
}

fn native_error(error: crate::interchange::Error) -> ContractError {
    match error.code {
        "limit" => ContractError::Limit("native instrument checking exceeded its bounded profile"),
        "contract" => ContractError::EquationMismatch,
        _ => ContractError::InvalidCircuit(error.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::{DEFAULT_EXACT_WORK, FunctionIdentity};
    use crate::ir::*;

    fn work() -> Budget {
        Budget::new(DEFAULT_EXACT_WORK)
    }
    fn signature() -> Signature {
        Signature {
            input: BasisType::Bit,
            result: vec![ResultAtom::Bit],
        }
    }
    fn identity() -> RetainedIdentity {
        RetainedIdentity::Owned(FunctionIdentity {
            implementation: "implementation".into(),
            specification: "reference".into(),
            sources: vec![("main".into(), "the exact original source snapshot".into())],
        })
    }
    fn readout(flip: bool) -> RawProgram {
        let mut operations = vec![RawOp::MeasureZ {
            input: TokenId(7),
            output: ClassicalId(3),
        }];
        if flip {
            operations.push(RawOp::ClassicalNot {
                input: ClassicalId(3),
                output: ClassicalId(9),
            });
        }
        RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(7),
                wires: vec![WireId(5)],
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(if flip { 9 } else { 3 })],
            declared_effect: Effect::Observe,
        }
    }

    #[test]
    fn instrument_receipts_bind_original_bytes_and_fresh_call_decisions() {
        let kernel = Kernel::selected().unwrap();
        let raw = readout(false);
        let original = kernel.accept_raw(raw.clone()).unwrap();
        let pair = Arc::new(
            InstrumentEvidence::check(
                &kernel,
                signature(),
                signature(),
                &original,
                &original,
                identity(),
                &mut work(),
            )
            .unwrap(),
        );
        assert_eq!(pair.native.artifact(), original.artifact());
        let request = crate::interchange::json::parse(pair.native.request().unwrap()).unwrap();
        assert_eq!(
            request
                .field("expected_artifact")
                .unwrap()
                .text()
                .unwrap()
                .as_bytes(),
            original.artifact()
        );
        let mut budget = work();
        let call = pair
            .check_call(
                &kernel,
                &signature(),
                &raw,
                ("main".into(), 10, 20),
                &mut budget,
            )
            .unwrap();
        assert!(Arc::ptr_eq(&call.pair, &pair));
        assert!(budget.remaining() < DEFAULT_EXACT_WORK - call.native.exact_work());
        assert_eq!(call.native.artifact(), original.artifact());
        assert!(matches!(
            pair.check_call(
                &kernel,
                &signature(),
                &readout(true),
                ("main".into(), 10, 20),
                &mut work()
            ),
            Err(ContractError::EquationMismatch)
        ));
        let wrong = Signature {
            input: BasisType::Bit,
            result: vec![ResultAtom::Pair, ResultAtom::Bit, ResultAtom::Unit],
        };
        assert!(
            pair.check_call(&kernel, &wrong, &raw, ("main".into(), 10, 20), &mut work())
                .is_err()
        );
        let missing = Kernel::new("/nonexistent/qleisli-instrument-checker");
        assert!(matches!(
            pair.check_call(
                &missing,
                &signature(),
                &raw,
                ("main".into(), 10, 20),
                &mut work()
            ),
            Err(ContractError::InvalidCircuit(_))
        ));
        assert!(
            pair.check_call(
                &kernel,
                &signature(),
                &raw,
                ("main".into(), 10, 20),
                &mut Budget::new(0)
            )
            .is_err()
        );
        // The ordinary handle is still bound to request-free whole-root bytes.
        for source in [
            ("wrong-source".into(), 10, 20),
            ("main".into(), 20, 10),
            ("main".into(), 10, 100),
        ] {
            assert!(matches!(
                pair.check_call(&kernel, &signature(), &raw, source, &mut work()),
                Err(ContractError::EvidenceMismatch)
            ));
        }
        assert!(original.request().is_none());
    }

    #[test]
    fn instrument_wire_preserves_bits_zero_and_zero_owner_result_trees() {
        let kernel = Kernel::selected().unwrap();
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![WireId(0)],
                shape: BasisShape::BIT,
            }],
            classical_inputs: vec![],
            operations: vec![
                RawOp::Discard { input: TokenId(0) },
                RawOp::PackUnit { output: TokenId(1) },
            ],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Observe,
        };
        let original = kernel.accept_raw(raw.clone()).unwrap();
        let signature = || Signature {
            input: BasisType::Bit,
            result: vec![
                ResultAtom::Tuple(3),
                ResultAtom::Unit,
                ResultAtom::Bits(0),
                ResultAtom::Quantum(BasisType::Unit),
            ],
        };
        let pair = Arc::new(
            InstrumentEvidence::check(
                &kernel,
                signature(),
                signature(),
                &original,
                &original,
                identity(),
                &mut work(),
            )
            .unwrap(),
        );
        let request = crate::interchange::json::parse(pair.native.request().unwrap()).unwrap();
        let result = request
            .field("actual_signature")
            .unwrap()
            .field("result")
            .unwrap();
        assert_eq!(result.field("tag").unwrap().text().unwrap(), "tuple");
        let fields = result.field("fields").unwrap().array().unwrap();
        assert_eq!(fields[1].field("tag").unwrap().text().unwrap(), "bits");
        assert_eq!(fields[1].field("width").unwrap().number().unwrap(), 0);
        assert_eq!(
            fields[2]
                .field("basis")
                .unwrap()
                .field("tag")
                .unwrap()
                .text()
                .unwrap(),
            "unit"
        );
        pair.check_call(
            &kernel,
            &pair.signature,
            &raw,
            ("main".into(), 10, 20),
            &mut work(),
        )
        .unwrap();
    }

    #[test]
    fn instrument_signature_preflights_frontiers_depth_and_zero_width_types() {
        let good = Signature {
            input: BasisType::Bits(0),
            result: vec![
                ResultAtom::Tuple(3),
                ResultAtom::Unit,
                ResultAtom::Bits(0),
                ResultAtom::Quantum(BasisType::Unit),
            ],
        };
        good.validate(&mut work()).unwrap();
        for result in [
            vec![],
            vec![ResultAtom::Tuple(usize::MAX)],
            vec![ResultAtom::Pair, ResultAtom::Bit],
            vec![ResultAtom::Bit, ResultAtom::Unit],
            vec![ResultAtom::Tuple(2), ResultAtom::Bit, ResultAtom::Bit],
        ] {
            assert!(
                Signature {
                    input: BasisType::Bit,
                    result
                }
                .validate(&mut work())
                .is_err()
            );
        }
        let mut input = BasisType::Unit;
        for _ in 0..64 {
            input = BasisType::pair(input, BasisType::Unit);
        }
        assert!(
            Signature {
                input,
                result: vec![ResultAtom::Unit]
            }
            .validate(&mut work())
            .is_err()
        );
        assert!(good.validate(&mut Budget::new(1)).is_err());
        assert!(
            Signature {
                input: BasisType::Bit,
                result: vec![ResultAtom::Quantum(BasisType::Bits(7))]
            }
            .validate(&mut work())
            .is_err()
        );
    }
}
