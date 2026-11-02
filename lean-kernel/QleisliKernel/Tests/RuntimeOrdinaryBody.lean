import QleisliKernel.Qirf.RuntimeOrdinaryBody

/-! Original source events and actual literal gaps/observations on small data.
These components issue no source/runtime handle or global instrument proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinaryBody
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open QleisliKernel.Qirf RuntimeOrdinaryBody

private def gapProgram : Semantics.Observation.Program :=
  ⟨[⟨7,[],0⟩],[2],[.not 2 3],[7],[3],.unitary⟩

private def gapView := ((do
  let prepared ← RuntimeInterval.prepare [] gapProgram
  let before : RuntimeStructuralAction.SourceState :=
    ⟨[⟨⟨0,[.unit]⟩,⟨7,[],0⟩⟩],[⟨0,[.unit]⟩],1⟩
  let ordinary : RuntimeOrdinaryBody.State := ⟨[(2,.input 0)],[]⟩
  let checked ← RuntimeOrdinaryBody.readGap prepared.block 0 1 before ordinary
  return (checked.after.bindings.map (·.port.token),checked.after.issued.map (·.ordinal),
    checked.after.nextOrdinal,checked.ssa.table) : WorkM _).run 1000000).1.toOption

#guard gapView = some ([7],[0],1,[(2,.input 0),(3,.not (.input 0))])

-- The first bundled test is preserved at a85f9d7d. This separately labelled
-- component fixture declares its actual prelude policy and uses the fixed
-- native budget; it makes no bundled-standard-library coverage claim.
private def minimalSource (nested : Bool) : String :=
  "#![no_implicit_prelude]\n" ++
  if nested then "observe fn read(q:Q<Bit>)->Bit{measure_z(q)}pub observe fn route(q:Q<Bit>)->Bit{read(q)}"
  else "pub observe fn route(q:Q<Bit>)->Bit{measure_z(q)}"

private def program : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],[.measure 0 1],[],[1],.observe⟩

private def observedMinimal (nested : Bool) (bit : Bool) : Option (String × List String × List Nat × Nat) :=
  ((do
    let sources : Sources := #[("main",minimalSource nested)]
    let signature ← SourceRuntimeContext.readSignature sources "main" "route" {}
    let body ← SourceRuntimeTrace.readBodyWithSignature signature
    let prepared ← RuntimeInterval.prepare [] program
    let before : RuntimeStructuralAction.SourceState :=
      ⟨[⟨⟨0,[.bit]⟩,⟨0,[0],1⟩⟩],[⟨0,[.bit]⟩],1⟩
    let root : CallPath sources "main" "route" "main" "route" := .root body
    let ordinary ← match body.checked.events with
      | [.primitive event] => do
        let checked ← readObservation root event prepared.block ⟨event.call.calleeOffset,0,1⟩ before {}
        return checked.ordinary
      | [.named event] => do
        let callee ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
        let parent : CallPath sources "main" "route" "main" event.target.callerName ←
          if callerName : event.target.callerName = "route" then
            pure (by rw [callerName]; exact root)
          else throw .request
        let path := CallPath.named event callee.val (by with_reducible exact callee.property) parent
        let [.primitive measured] := callee.val.checked.events | throw .request
        let checked ← readObservation path measured prepared.block ⟨measured.call.calleeOffset,0,1⟩ before {}
        return checked.ordinary
      | _ => throw .request
    let [measurement] := ordinary.measurements | throw .request
    let values := valuation [] ordinary.measurements [(1,bit)]
    let [.ordinary [.bit] result] ← lift ((SourceRuntimeOrdinary.extract values body.checked.summary.value).mapError fun _ => .request)
      | throw .request
    return (measurement.origin.functionName,measurement.calls.map (·.functionName),
      [measurement.owner.ordinal],result) : WorkM _).run 10000000).1.toOption

#guard observedMinimal false false = some ("route",[],[0],0)
#guard observedMinimal false true = some ("route",[],[0],1)
#guard observedMinimal true false = some ("read",["route"],[0],0)
#guard observedMinimal true true = some ("read",["route"],[0],1)

#print axioms QleisliKernel.Qirf.RuntimeOrdinaryBody.Gap.sameSource
#print axioms QleisliKernel.Qirf.RuntimeOrdinaryBody.Observation.issuedUnchanged

end QleisliKernel.Tests.RuntimeOrdinaryBody
