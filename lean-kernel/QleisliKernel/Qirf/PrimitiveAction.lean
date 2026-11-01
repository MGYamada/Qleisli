import QleisliKernel.Qirf.PureInterval
import QleisliKernel.FiniteCarrier

/-! Literal existing primitive actions within a checked actual owner interval.
This checker requires the existing direct Raw lowering; an
optimized equivalent circuit needs its own checked transformation. Name/source
resolution is separate and cannot be inferred from matching these instructions.
This component alone grants no new primitive, inverse/control access or handle.
The port refinement uses the existing bounded finite-carrier reader. General
wide owner support remains a separate obligation; no issue scope is reduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.PrimitiveAction
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Finite

inductive Kind where
  | h | globalPhaseEighth
  | phase (exponent : Nat)
  deriving BEq, DecidableEq, Repr

/-- Existing Raw spellings used by the common emitter. The empty-axis
monomial is an exact scalar eighth turn, including on zero-width owners. -/
def operation (kind : Kind) (input output : Nat) : Semantics.Raw.Op :=
  match kind with
  | .h => .gate .h input output
  | .globalPhaseEighth => .applyUnitary input output [⟨[],.monomial [] [0] [1]⟩]
  | .phase exponent => .applyUnitary input output [⟨[],.monomial [0] [0,1] [0,exponent]⟩]

def typeMatches (kind : Kind) (role : Semantics.SourceOwners.Owner) : Prop :=
  match kind with
  | .h => role.basis = [.bit]
  | .globalPhaseEighth => True
  | .phase _ => role.basis = [.bit]

instance (kind : Kind) (role : Semantics.SourceOwners.Owner) : Decidable (typeMatches kind role) :=
  match kind with
  | .h => inferInstanceAs (Decidable (role.basis = [.bit]))
  | .globalPhaseEighth => inferInstanceAs (Decidable True)
  | .phase _ => inferInstanceAs (Decidable (role.basis = [.bit]))

structure Checked (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (start count input output : Nat)
    (role : Semantics.SourceOwners.Owner) (kind : Kind) where
  interval : Qirf.PureInterval.Many.Checked 1 dependencies program start count [input] [output] [role]
  layout : Qirf.PureInterval.Witness (FiniteCarrier.read role.basis)
  inputWidth : interval.selected.map (·.bits) = [layout.val.bits]
  outputWidth : interval.returned.map (·.bits) = [layout.val.bits]
  sourceType : typeMatches kind role
  instruction : interval.slice.operations = [operation kind input output]

/-- The source caller must independently bind the actual primitive name,
complete nominal role, occurrence and interval positions; fresh graph checking supplies dependencies.
The local layout-width checks do not identify equal-width source types.
Unknown functions or effects must not be routed here as a fallback. -/
def checkWith (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (start count input output : Nat)
    (role : Semantics.SourceOwners.Owner) (kind : Kind)
    (readInterval : WorkM (Qirf.PureInterval.Many.Checked 1 dependencies program
      start count [input] [output] [role])) :
    WorkM (Checked dependencies program start count input output role kind) := do
  exactWork (Exact.charge (role.basis.length+count+1))
  guard (count == 1) .request
  if sourceType : typeMatches kind role then
    let layout ← SourceTypes.NaturalAffine.witness (FiniteCarrier.read role.basis)
    let interval ← readInterval
    if inputWidth : interval.selected.map (·.bits) = [layout.val.bits] then
      if outputWidth : interval.returned.map (·.bits) = [layout.val.bits] then
        if instruction : interval.slice.operations = [operation kind input output] then
          return ⟨interval,layout,inputWidth,outputWidth,sourceType,instruction⟩
        else throw .equation
      else throw .request
    else throw .request
  else throw .request

/-- Standalone entrypoint retains its original work and error order. -/
def check (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (start count input output : Nat)
    (role : Semantics.SourceOwners.Owner) (kind : Kind) :
    WorkM (Checked dependencies program start count input output role kind) :=
  checkWith dependencies program start count input output role kind
    (Qirf.PureInterval.Many.check 1 dependencies program start count [input] [output] [role])

/-- Reuses only the exact whole/initial witnesses; the complete literal primitive
and interval obligations are checked by the same continuations. -/
def checkPrepared (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (prepared : Qirf.PureInterval.Many.Prepared dependencies program)
    (start count input output : Nat) (role : Semantics.SourceOwners.Owner) (kind : Kind) :
    WorkM (Checked dependencies program start count input output role kind) :=
  checkWith dependencies program start count input output role kind
    (Qirf.PureInterval.Many.checkPrepared 1 dependencies program prepared
      start count [input] [output] [role])

theorem Checked.originalInstruction {dependencies program start count input output role kind}
    (checked : Checked dependencies program start count input output role kind) :
    (program.operations.drop start).take count =
      [.pure (operation kind input output)] := by
  rw [checked.interval.slice.original,checked.instruction]
  rfl

theorem Checked.hRequiresBit {dependencies program start count input output role}
    (checked : Checked dependencies program start count input output role .h) :
    role.basis = [.bit] := checked.sourceType

end QleisliKernel.Qirf.PrimitiveAction
