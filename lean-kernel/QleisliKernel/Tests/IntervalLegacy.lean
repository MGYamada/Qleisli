import QleisliKernel.Qirf.PureInterval

/-! Frozen pre-sharing executable used only for the all-arity refinement proof.
It is not called by the shared interval checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.IntervalLegacy
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf.PureInterval
open QleisliKernel.Qirf.PureInterval.Many

/-- Dependencies and roles are not externally trusted: the caller must freshly
bind them to the actual graph and original source. Both whole and local checks
consume one work budget. Unknown source contexts cannot use this as a fallback. -/
def check (arity : Nat) (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (start count : Nat) (inputs outputs : List Nat) (roles : List Semantics.SourceOwners.Owner) :
    WorkM (Checked arity dependencies program start count inputs outputs roles) := do
  guard (arity ≤ 128) .limit
  exactWork (Exact.charge (8*(program.operations.length+inputs.length+outputs.length+roles.length+1)))
  if bounded : start+count ≤ program.operations.length then
    if arity : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity then
      let whole ← SourceTypes.NaturalAffine.witness (Raw.Observation.verify dependencies program)
      let entry ← SourceTypes.NaturalAffine.witness (initial program)
      let before ← SourceTypes.NaturalAffine.witness
        (Raw.Observation.checkOps dependencies 65 entry.val (program.operations.take start))
      let slice ← readSlice program start count
      let after ← SourceTypes.NaturalAffine.witness
        (Raw.Observation.checkOps dependencies 65 before.val ((program.operations.drop start).take count))
      exactWork (Exact.charge (32*(before.val.quantum.live.length+after.val.quantum.live.length+1)))
      match atEntry : ports before.val inputs with
      | none => throw .request
      | some selected =>
        let pureBody ← SourceTypes.NaturalAffine.witness
          (Raw.Pure.verify dependencies (fragment selected slice outputs))
        let ownerReturn ← Raw.OwnerFlow.check roles roles (fragment selected slice outputs)
        match rawExit : portsOf pureBody.val.state.live outputs with
        | none => throw .request
        | some returned =>
          if atExit : ports after.val outputs = some returned then
            if retained : spectators before.val inputs = spectators after.val outputs then
              return ⟨bounded,arity,whole,entry,before,slice,after,selected,atEntry,pureBody,
                ownerReturn.down,returned,rawExit,atExit,retained⟩
            else throw .request
          else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Tests.IntervalLegacy
