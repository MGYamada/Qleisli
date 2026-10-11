//! Transport of bounded complete source types for observing equations.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::types::{Kind, Type};
use crate::contract::exact::Budget;
use crate::contract::instrument::{ResultAtom, Signature};
use crate::contract::{BasisType, ContractError};

pub(super) fn signature<N>(
    parameters: &[Type<N>],
    output: &Type<N>,
    natural: impl Fn(&N) -> Option<u32>,
    budget: &mut Budget,
) -> Result<Signature, ContractError> {
    let [input] = parameters else {
        return Err(ContractError::Type(
            "instrument contracts require one quantum argument",
        ));
    };
    let Kind::Q(input) = &input.kind else {
        return Err(ContractError::Type(
            "instrument contracts require one quantum argument",
        ));
    };
    for root in [input.as_ref(), output] {
        let mut pending = vec![(root, 1)];
        let mut count = 0usize;
        while let Some((ty, depth)) = pending.pop() {
            budget.charge(1)?;
            count += 1;
            if count > 4096 || depth > 64 {
                return Err(ContractError::Limit(
                    "instrument source type exceeds 4096 nodes or depth 64",
                ));
            }
            match &ty.kind {
                Kind::Q(basis) => {
                    if count + pending.len() + 1 > 4096 {
                        return Err(ContractError::Limit(
                            "instrument source type exceeds 4096 nodes",
                        ));
                    }
                    pending.push((basis, depth + 1));
                }
                Kind::Tuple(fields) => {
                    if fields.len() > 4096 - count - pending.len() {
                        return Err(ContractError::Limit(
                            "instrument source tuple exceeds 4096 nodes",
                        ));
                    }
                    budget.charge(fields.len())?;
                    pending.extend(fields.iter().rev().map(|ty| (ty, depth + 1)));
                }
                _ => {}
            }
        }
    }
    fn basis<N>(
        ty: &Type<N>,
        natural: &impl Fn(&N) -> Option<u32>,
    ) -> Result<BasisType, ContractError> {
        Ok(match &ty.kind {
            Kind::Unit => BasisType::Unit,
            Kind::Bit => BasisType::Bit,
            Kind::Bits(n) => BasisType::Bits(
                natural(n).ok_or(ContractError::Type("instrument size must be closed"))?,
            ),
            Kind::Tuple(fields) => {
                let mut values = fields
                    .iter()
                    .map(|ty| basis(ty, natural))
                    .collect::<Result<Vec<_>, _>>()?;
                if values.len() == 2 {
                    let right = values.pop().expect("pair right");
                    BasisType::pair(values.pop().expect("pair left"), right)
                } else if values.len() >= 3 {
                    BasisType::Tuple(values)
                } else {
                    return Err(ContractError::Type(
                        "instrument tuple requires at least two fields",
                    ));
                }
            }
            _ => {
                return Err(ContractError::Type(
                    "instrument requires a finite quantum basis",
                ));
            }
        })
    }
    let input = basis(input, &natural)?;
    let mut result = Vec::new();
    let mut pending = vec![output];
    while let Some(ty) = pending.pop() {
        result.push(match &ty.kind {
            Kind::Unit => ResultAtom::Unit,
            Kind::Bit => ResultAtom::Bit,
            Kind::Bits(n) => ResultAtom::Bits(
                natural(n).ok_or(ContractError::Type("instrument size must be closed"))?,
            ),
            Kind::Q(ty) => ResultAtom::Quantum(basis(ty, &natural)?),
            Kind::Tuple(fields) if fields.len() >= 2 => {
                pending.extend(fields.iter().rev());
                if fields.len() == 2 {
                    ResultAtom::Pair
                } else {
                    ResultAtom::Tuple(fields.len())
                }
            }
            _ => {
                return Err(ContractError::Type(
                    "instrument result must be a closed finite value type",
                ));
            }
        });
    }
    let signature = Signature { input, result };
    signature.validate(budget)?;
    Ok(signature)
}
