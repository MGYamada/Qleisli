//! Common source typing for language-owned primitive identities; no new native acceptance rule.
use super::*;

pub(in crate::frontend) use crate::frontend::primitive::PrimitiveId as Primitive;

impl Primitive {
    pub(in crate::frontend) fn dependent(self) -> bool {
        matches!(
            self,
            Self::GlobalPhaseEighth | Self::Split | Self::Join | Self::Discard
        )
    }
    pub(in crate::frontend) fn fixed(
        self,
        ns: &[Linear],
        context: &Context,
        span: Span,
        budget: &Budget,
    ) -> Result<(Vec<Ty>, Ty)> {
        if ns.len() != self.natural_arity() {
            return Err(SourceError::new(
                "static-arity",
                span,
                "primitive static argument arity mismatch",
            ));
        }
        let cells = match self {
            Self::H | Self::Phase => 5,
            Self::MeasureZ | Self::Unit | Self::Finish => 4,
            Self::TakeBit | Self::PutBit => 8,
            Self::EmptyBits => 1,
            Self::PrependBit => 5,
            Self::GlobalPhaseEighth | Self::Split | Self::Join | Self::Discard => {
                return Err(SourceError::new(
                    "type",
                    span,
                    "primitive requires its actual inferred quantum input type",
                ));
            }
        };
        budget.charge(span, cells)?;
        let mut charge = |span, cells| budget.preparation_charge(span, cells);
        let qbit = || Ty::quantum(Ty::bit());
        let (input, output) = match self {
            Self::H | Self::Phase => (vec![qbit()], qbit()),
            Self::MeasureZ => (vec![qbit()], Ty::bit()),
            Self::TakeBit | Self::PutBit => {
                let one = Linear::constant_budgeted(1, span, &mut charge)?;
                if !context.proves_le_budgeted(
                    &ns[1].add_budgeted(&one, span, &mut charge)?,
                    &ns[0],
                    span,
                    "register index needs k < n",
                    &mut charge,
                )? {
                    return Err(SourceError::new("size", span, "register index needs k < n"));
                }
                let n = ns[0].copy_budgeted(span, &mut charge)?;
                let rest = ns[0].sub_budgeted(&one, span, &mut charge)?;
                if self == Self::TakeBit {
                    (
                        vec![Ty::quantum(Ty::bits(n))],
                        Ty::pair(qbit(), Ty::quantum(Ty::bits(rest))),
                    )
                } else {
                    (
                        vec![qbit(), Ty::quantum(Ty::bits(rest))],
                        Ty::quantum(Ty::bits(n)),
                    )
                }
            }
            Self::EmptyBits => (
                vec![],
                Ty::bits(Linear::constant_budgeted(0, span, &mut charge)?),
            ),
            Self::PrependBit => (
                vec![Ty::bit(), Ty::bits(ns[0].copy_budgeted(span, &mut charge)?)],
                Ty::bits(ns[0].add_budgeted(
                    &Linear::constant_budgeted(1, span, &mut charge)?,
                    span,
                    &mut charge,
                )?),
            ),
            Self::Unit => (vec![Ty::unit()], Ty::quantum(Ty::unit())),
            Self::Finish => (vec![Ty::quantum(Ty::unit())], Ty::unit()),
            Self::GlobalPhaseEighth | Self::Split | Self::Join | Self::Discard => {
                return Err(SourceError::new(
                    "type",
                    span,
                    "primitive requires its actual inferred quantum input type",
                ));
            }
        };
        for ty in input.iter().chain([&output]) {
            budget.ty(span, ty)?;
        }
        Ok((input, output))
    }
    pub(in crate::frontend) fn output(
        self,
        input: Vec<Ty>,
        span: Span,
        budget: &Budget,
    ) -> Result<Ty> {
        if input.len() != self.runtime_arity() {
            return Err(SourceError::new(
                "arity",
                span,
                "runtime argument arity mismatch",
            ));
        }
        for ty in &input {
            budget.ty(span, ty)?;
        }
        match self {
            Self::GlobalPhaseEighth | Self::Discard => {
                if !input[0].is_quantum_owner() {
                    return Err(SourceError::new(
                        "type",
                        span,
                        "primitive requires one exact quantum owner",
                    ));
                }
                if self == Self::Discard {
                    Ok(Ty::unit())
                } else {
                    Ok(input.into_iter().next().expect("one checked owner"))
                }
            }
            Self::Split => {
                let fields = input[0]
                    .quantum_basis()
                    .and_then(Type::tuple_fields)
                    .filter(|f| f.len() == 2)
                    .ok_or_else(|| SourceError::new("type", span, "split requires Q<(A, B)>"))?;
                budget.charge(span, 3)?;
                Ok(Ty::pair(
                    Ty::quantum(budget.copy_ty(span, &fields[0])?),
                    Ty::quantum(budget.copy_ty(span, &fields[1])?),
                ))
            }
            Self::Join => {
                let a = input[0].quantum_basis().ok_or_else(|| {
                    SourceError::new("type", span, "join requires two quantum owners")
                })?;
                let b = input[1].quantum_basis().ok_or_else(|| {
                    SourceError::new("type", span, "join requires two quantum owners")
                })?;
                let a_size = type_size_budgeted(a, 4096, 64, true, span, &mut |span, cells| {
                    budget.charge(span, cells)
                })?;
                let b_size = type_size_budgeted(b, 4096, 64, true, span, &mut |span, cells| {
                    budget.charge(span, cells)
                })?;
                if a_size.nodes + b_size.nodes + 1 > 4096 || a_size.depth.max(b_size.depth) + 1 > 64
                {
                    return Err(SourceError::new(
                        "limit",
                        span,
                        "joined basis exceeds type capacity",
                    ));
                }
                budget.charge(span, 2)?;
                Ok(Ty::quantum(Ty::pair(
                    budget.copy_ty(span, a)?,
                    budget.copy_ty(span, b)?,
                )))
            }
            _ => Err(SourceError::new(
                "type",
                span,
                "fixed primitive requires its checked signature",
            )),
        }
    }
}
