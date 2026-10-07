//! Typed union of existing sealed source names; no new native acceptance rule.
use super::*;
use crate::ir::Effect;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum Primitive {
    H,
    X,
    Z,
    T,
    S,
    Sdg,
    Tdg,
    Id,
    PhaseEighth,
    Init0,
    Cnot,
    Toffoli,
    Split,
    Join,
    MeasureZ,
    Reset,
    Discard,
    Phase,
    ControlledPhase,
    TakeBit,
    PutBit,
    Empty,
    ConsumeEmpty,
    EmptyBits,
    PrependBit,
    Unit,
    Finish,
}
impl Primitive {
    pub const ALL: &'static [Self] = &[
        Self::H,
        Self::X,
        Self::Z,
        Self::T,
        Self::S,
        Self::Sdg,
        Self::Tdg,
        Self::Id,
        Self::PhaseEighth,
        Self::Init0,
        Self::Cnot,
        Self::Toffoli,
        Self::Split,
        Self::Join,
        Self::MeasureZ,
        Self::Reset,
        Self::Discard,
        Self::Phase,
        Self::ControlledPhase,
        Self::TakeBit,
        Self::PutBit,
        Self::Empty,
        Self::ConsumeEmpty,
        Self::EmptyBits,
        Self::PrependBit,
        Self::Unit,
        Self::Finish,
    ];
    pub fn path(self) -> &'static str {
        match self {
            Self::H => "std::quantum::h",
            Self::X => "std::quantum::x",
            Self::Z => "std::quantum::z",
            Self::T => "std::quantum::t",
            Self::S => "std::quantum::s",
            Self::Sdg => "std::quantum::sdg",
            Self::Tdg => "std::quantum::tdg",
            Self::Id => "std::quantum::id",
            Self::PhaseEighth => "std::quantum::phase_eighth",
            Self::Init0 => "std::quantum::init0",
            Self::Cnot => "std::quantum::cnot",
            Self::Toffoli => "std::quantum::toffoli",
            Self::Split => "std::quantum::split",
            Self::Join => "std::quantum::join",
            Self::MeasureZ => "std::observe::measure_z",
            Self::Reset => "std::observe::reset",
            Self::Discard => "std::observe::discard",
            Self::Phase => "std::quantum::phase",
            Self::ControlledPhase => "std::quantum::controlled_phase",
            Self::TakeBit => "std::registers::take_bit",
            Self::PutBit => "std::registers::put_bit",
            Self::Empty => "std::registers::empty",
            Self::ConsumeEmpty => "std::registers::consume_empty",
            Self::EmptyBits => "std::classical::empty_bits",
            Self::PrependBit => "std::classical::prepend_bit",
            Self::Unit => "std::quantum::unit",
            Self::Finish => "std::quantum::finish",
        }
    }
    pub fn lookup(path: &str) -> Option<Self> {
        Self::ALL.iter().copied().find(|p| p.path() == path)
    }
    pub fn effect(self) -> Effect {
        match self {
            Self::Init0 => Effect::Iso,
            Self::MeasureZ | Self::Reset | Self::Discard => Effect::Observe,
            _ => Effect::Unitary,
        }
    }
    pub fn natural_arity(self) -> usize {
        match self {
            Self::Phase | Self::ControlledPhase | Self::TakeBit | Self::PutBit => 2,
            Self::PrependBit => 1,
            _ => 0,
        }
    }
    pub fn runtime_arity(self) -> usize {
        match self {
            Self::Init0 | Self::Empty | Self::EmptyBits => 0,
            Self::Cnot | Self::ControlledPhase | Self::PutBit | Self::Join | Self::PrependBit => 2,
            Self::Toffoli => 3,
            _ => 1,
        }
    }
    pub fn dependent(self) -> bool {
        matches!(
            self,
            Self::Id | Self::PhaseEighth | Self::Split | Self::Join | Self::Discard
        )
    }
    pub fn fixed(
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
            Self::H
            | Self::X
            | Self::Z
            | Self::T
            | Self::S
            | Self::Sdg
            | Self::Tdg
            | Self::Phase
            | Self::Reset => 5,
            Self::Init0 | Self::Empty => 2,
            Self::Cnot | Self::ControlledPhase => 11,
            Self::Toffoli => 17,
            Self::MeasureZ | Self::ConsumeEmpty | Self::Unit | Self::Finish => 4,
            Self::TakeBit | Self::PutBit => 8,
            Self::EmptyBits => 1,
            Self::PrependBit => 5,
            Self::Id | Self::PhaseEighth | Self::Split | Self::Join | Self::Discard => {
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
            Self::H
            | Self::X
            | Self::Z
            | Self::T
            | Self::S
            | Self::Sdg
            | Self::Tdg
            | Self::Phase
            | Self::Reset => (vec![qbit()], qbit()),
            Self::Init0 => (vec![], qbit()),
            Self::Cnot | Self::ControlledPhase => (vec![qbit(), qbit()], Ty::pair(qbit(), qbit())),
            Self::Toffoli => (
                vec![qbit(), qbit(), qbit()],
                Ty::pair(Ty::pair(qbit(), qbit()), qbit()),
            ),
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
            Self::Empty => (
                vec![],
                Ty::quantum(Ty::bits(Linear::constant_budgeted(0, span, &mut charge)?)),
            ),
            Self::ConsumeEmpty => (
                vec![Ty::quantum(Ty::bits(Linear::constant_budgeted(
                    0,
                    span,
                    &mut charge,
                )?))],
                Ty::unit(),
            ),
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
            Self::Id | Self::PhaseEighth | Self::Split | Self::Join | Self::Discard => {
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
    pub fn output(self, input: Vec<Ty>, span: Span, budget: &Budget) -> Result<Ty> {
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
            Self::Id | Self::PhaseEighth | Self::Discard => {
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
