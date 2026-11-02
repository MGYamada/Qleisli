import QleisliKernel.Qirf.RuntimeSourceBoundary

/-! Nested runtime output forests and distinct zero-width source owners.
Only structural boundary matching is exercised; source expression/history
and operator correspondence remain required outside this component.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeSourceBoundary
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf

private def owner (ordinal : Nat) : Semantics.SourceOwners.Owner := ⟨ordinal,[.unit]⟩
private def port (token : Nat) : Semantics.Raw.Port := ⟨token,[],0⟩
private def quantum (token : Nat) : Semantics.RuntimeStorage.Atom :=
  .quantum ⟨port token,[.unit]⟩

private def value : SourceTypes.SourceRuntimeValues.Value :=
  [.tuple 2,.tuple 2,.owner (owner 1),.owner (owner 0),.ordinary [.bit] (.input 0)]

private def program : Semantics.Observation.Program :=
  ⟨[port 0,port 1],[9],[],[1,0],[9],.unitary⟩

private def stored (swapped : Bool) : Semantics.RuntimeStorage.Value :=
  [.tuple 2,.tuple 2,quantum (if swapped then 0 else 1),quantum (if swapped then 1 else 0),
    .ordinary [.bit] (.bit 9)]

private def boundary (storage : Semantics.RuntimeStorage.Value) (tokens : List Nat) : WorkM Unit := do
  let prepared ← RuntimeInterval.prepare [] program
  let owners ← RuntimeOwnerMap.check [owner 1,owner 0] prepared.whole.state
    [⟨owner 1,port 1⟩,⟨owner 0,port 0⟩]
  let _ ← RuntimeSourceBoundary.readOutputs value prepared.whole.state owners storage tokens
  return ()

#guard (boundary (stored false) [1,0]).run 100000 |>.1.toOption.isSome

#guard (match (boundary (stored true) [0,1]).run 100000 with
  | (.error .request,_) => true
  | _ => false)

#guard (match (boundary (stored false) [0,1]).run 100000 with
  | (.error .request,_) => true
  | _ => false)

-- The same owner and classical projections cannot repair a different outer
-- result tree. No source or retained storage is rewritten to flatten it.
#guard (match (boundary [.tuple 3,quantum 1,quantum 0,.ordinary [.bit] (.bit 9)] [1,0]).run 100000 with
  | (.error .request,_) => true
  | _ => false)

end QleisliKernel.Tests.RuntimeSourceBoundary
