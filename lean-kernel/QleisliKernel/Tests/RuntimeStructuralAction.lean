import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.RuntimeRegisterAction
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

private def register {α : Type} (text : String) (inputs : List Semantics.Raw.Port)
    (ops : List Semantics.Raw.Op) (outputs : List Nat)
    (report : List Semantics.Raw.Port → RuntimeOwnerMap.Map → α) : WorkM α := do
  let sources : Sources := #[("main","#![no_implicit_prelude]\n" ++ text)]
  let signature ← SourceRuntimeContext.readSignature sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.registerPrimitive event] := body.checked.events | throw .request
  let program : Semantics.Observation.Program := ⟨inputs,[],ops.map .pure,outputs,[],.unitary⟩
  let prepared ← RuntimeInterval.prepare [] program
  let interval ← RuntimeInterval.check prepared.block 0 ops.length
  let roles := body.checked.summary.parameterValues.flatMap valueOwners
  guard (roles.length == inputs.length) .request
  let previous := (roles.zip inputs).map fun (owner,port) => (⟨owner,port⟩ : RuntimeOwnerMap.Binding)
  let before : RuntimeStructuralAction.SourceState := ⟨previous,roles,body.checked.summary.nextOwner⟩
  let checked ← RuntimeRegisterAction.read interval event before
  return report checked.outputs checked.after.bindings

private def take (width offset actual : Nat) (wires : List Nat) := register
  (s!"pub unitary fn main(q:Q<Bits<{width}>>,s:Q<Unit>)->((Q<Bit>,Q<Bits<{width-1}>>),Q<Unit>)" ++
    "{" ++ s!"(take_bit[{width},{offset}](q),s)" ++ "}")
  [port 0 wires,port 1 []] [.split 0 2 3 actual,.split 3 4 5 1,.join 2 5 6] [4,6,1]
  (fun outputs frame => (outputs.map (·.wires),frame.map (·.port.token)))

#guard ((take 3 1 1 [8,2,6]).run 1000000).1.toOption == some ([[2],[8,6]],[1,4,6])
#guard (match (take 3 1 0 [8,2,6]).run 1000000 with | (.error .request,_) => true | _ => false)
#guard ((take 1 0 0 [8]).run 1000000).1.toOption == some ([[8],[]],[1,4,6])

private def put (reverse : Bool) := register
  "pub unitary fn main(b:Q<Bit>,q:Q<Bits<2>>)->Q<Bits<3>>{put_bit[3,1](b,q)}"
  [port 0 [2],port 1 [8,6]]
  [.split 1 2 3 1,.join (if reverse then 0 else 2) (if reverse then 2 else 0) 4,.join 4 3 5] [5]
  (fun outputs _ => outputs.map (·.wires))

#guard ((put false).run 1000000).1.toOption == some [[8,2,6]]
#guard (match (put true).run 1000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.RuntimeStructuralAction
