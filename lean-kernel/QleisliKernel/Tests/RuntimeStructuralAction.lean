import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Small original-source/actual-Raw structural transports. Equal zero-width
ports cannot choose owner order, a wrong split boundary remains invalid, and
release does not rewind the source identity history. No execution handle or
maximum-size quantum instance is constructed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStructuralAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open QleisliKernel.Qirf SourceRuntimeValues

private def port (token : Nat) (wires : List Nat) : Semantics.Raw.Port := ⟨token,wires,wires.length⟩

private def checked (text : String) (inputs : List Semantics.Raw.Port)
    (operations : List Semantics.Raw.Op) (outputs : List Nat) : WorkM (List Nat × List Nat) := do
  let sources : Sources := #[("main","#![no_implicit_prelude]\n" ++ text)]
  let signature ← SourceRuntimeContext.readSignature sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let program : Semantics.Observation.Program := ⟨inputs,[],operations.map .pure,outputs,[],.unitary⟩
  let prepared ← RuntimeInterval.prepare [] program
  let roles := body.checked.summary.parameterValues.flatMap valueOwners
  guard (roles.length == inputs.length && body.checked.events.length == operations.length) .request
  let bindings := (roles.zip inputs).map fun (owner,port) => (⟨owner,port⟩ : RuntimeOwnerMap.Binding)
  let before : RuntimeStructuralAction.SourceState := ⟨bindings,roles,body.checked.summary.nextOwner⟩
  let after ← body.checked.events.zipIdx.foldlM (fun before (event,index) => do
    let .primitive event := event | throw .request
    let action ← RuntimeStructuralAction.read prepared.block index 1 event before
    pure action.after) before
  return (after.issued.map (·.ordinal),after.bindings.map (·.owner.ordinal))

private def joinUnits (swap : Bool) := checked
  "pub unitary fn main(a:Q<Unit>,b:Q<Unit>)->Q<(Unit,Unit)>{join(a,b)}"
  [port 0 [],port 1 []] [.join (if swap then 1 else 0) (if swap then 0 else 1) 2] [2]

#guard (joinUnits false).run 10000000 |>.1.toOption == some ([0,1,2],[2])
#guard (match (joinUnits true).run 10000000 with | (.error .request,_) => true | _ => false)

private def splitUnitBit (wrongBoundary : Bool) := checked
  "pub unitary fn main(q:Q<(Unit,Bit)>)->(Q<Unit>,Q<Bit>){split(q)}"
  [port 0 [0]] [.split 0 1 2 (if wrongBoundary then 1 else 0)] [1,2]

#guard (splitUnitBit false).run 10000000 |>.1.toOption == some ([0,1,2],[1,2])
#guard (match (splitUnitBit true).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (checked "pub unitary fn main()->Q<Unit>{unit(())}" [] [.packUnit 0] [0]).run
  10000000 |>.1.toOption == some ([0],[0])
#guard (checked "pub unitary fn main(u:Q<Unit>)->Q<Unit>{finish(u);unit(())}"
  [port 0 []] [.unpackUnit 0,.packUnit 1] [1]).run 10000000 |>.1.toOption == some ([0,1],[1])

end QleisliKernel.Tests.RuntimeStructuralAction
