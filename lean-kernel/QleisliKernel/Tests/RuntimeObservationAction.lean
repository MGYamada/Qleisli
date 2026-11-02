import QleisliKernel.Qirf.RuntimeObservationAction
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Tests.SourceTraceOriginals

/-! Fresh original destructive source events against actual small Raw bodies.
No native execution handle or complete ordinary-history proof is issued here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeObservationAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf QleisliKernel.SourceTypes

private def text := "pub observe fn route(q:Q<Bit>,r:Q<Bit>,u:Q<Unit>)->(Bit,(Q<Bit>,Q<Unit>)){(measure_z(q),(r,u))}"
private def sources : Sources := #[("main",text)] ++ SourceTraceOriginals.bundled
private def first : Semantics.Raw.Port := ⟨0,[0],1⟩
private def second : Semantics.Raw.Port := ⟨1,[1],1⟩
private def empty : Semantics.Raw.Port := ⟨2,[],0⟩

private def program (wrongOwner : Bool) : Semantics.Observation.Program :=
  ⟨[first,second,empty],[],[.measure (if wrongOwner then 1 else 0) 7],
    [if wrongOwner then 0 else 1,2],[7],.observe⟩

private def inputStorage : List Semantics.RuntimeStorage.Value :=
  [[.quantum ⟨first,[.bit]⟩],[.quantum ⟨second,[.bit]⟩],[.quantum ⟨empty,[.unit]⟩]]

private def bound (wrongOwner : Bool) (functionName : String := "route") : WorkM Bool := do
  let signature ← SourceRuntimeContext.readSignature sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let root ← RuntimeInterval.prepare [] (program wrongOwner)
  let inputs ← RuntimeSourceBoundary.readInputs body root inputStorage
  match body.checked.events with
  | [.primitive event] =>
    let action ← Qirf.RuntimeObservationAction.check functionName event root.block
      ⟨event.call.calleeOffset,0,1⟩ inputs.owners.bindings
    return (match action.measurement with
      | some (.measured site [] operand,id) =>
        site.moduleName == "main" && site.functionName == "route" && operand.ordinal == 0 && id == 7
      | _ => false) && action.after.bindings.any (fun binding =>
        binding.owner.ordinal == 2 && binding.port.token == 2 && binding.port.wires.isEmpty)
  | _ => throw .request

#guard (bound false).run 2000000000 |>.1.toOption == some true

-- Both candidate bodies obey Raw ownership and observation. The wrong one
-- measures the equal-width caller spectator instead of the original operand.
#guard (RuntimeInterval.prepare [] (program true)).run 100000 |>.1.toOption.isSome
#guard (match (bound true).run 2000000000 with
  | (.error .request,_) => true
  | _ => false)

#guard (match (bound false "other").run 2000000000 with
  | (.error .request,_) => true
  | _ => false)

end QleisliKernel.Tests.RuntimeObservationAction
