import QleisliKernel.Qirf.RuntimeOwnerPhis

/-! Zero-qubit owner identities still determine both branch phi operands.
These component controls do not supply an original source-body judgment.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOwnerPhis
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf

private def owner (ordinal : Nat) : Semantics.SourceOwners.Owner := ⟨ordinal,[.unit]⟩
private def port (token : Nat) : Semantics.Raw.Port := ⟨token,[],0⟩

private def original : List SourceTypes.SourceRuntimeBranches.Phi :=
  [⟨owner 2,owner 0,owner 0,rfl,rfl⟩,⟨owner 3,owner 1,owner 1,rfl,rfl⟩]

private def program (swapped : Bool) : Semantics.Observation.Program :=
  ⟨[port 0,port 1],[],
    [.constant true 20,
      .branch 20 [.pure (.join 0 1 2),.pure (.split 2 3 4 0)]
        [.pure (.join 0 1 5),.pure (.split 5 6 7 0)]
        [⟨3,if swapped then 7 else 6,8,[]⟩,⟨4,if swapped then 6 else 7,9,[]⟩] []],
    [8,9],[],.unitary⟩

private def bind (swapped : Bool) : WorkM (List Nat) := do
  let prepared ← RuntimeInterval.prepare [] (program swapped)
  let actual ← RuntimeInterval.readBranch prepared.block 1
  let left ← RuntimeOwnerMap.check [owner 0,owner 1] actual.thenState
    [⟨owner 0,port 3⟩,⟨owner 1,port 4⟩]
  let right ← RuntimeOwnerMap.check [owner 0,owner 1] actual.elseState
    [⟨owner 0,port 6⟩,⟨owner 1,port 7⟩]
  let bound ← RuntimeOwnerPhis.check actual original [] [owner 0,owner 1] [owner 0,owner 1]
    [owner 2,owner 3] left right
  return bound.output.bindings.map (·.port.token)

#guard (bind false).run 200000 |>.1.toOption == some [8,9]

-- The mutated program remains a valid zero-width Raw branch. Its wrong phi
-- cannot be hidden by the equal physical widths or the known-true condition.
#guard (RuntimeInterval.prepare [] (program true)).run 200000 |>.1.toOption.isSome
#guard (match (bind true).run 200000 with
  | (.error .request,_) => true
  | _ => false)

#guard (match (do
    let prepared ← RuntimeInterval.prepare [] (program false)
    let actual ← RuntimeInterval.readBranch prepared.block 1
    let _ ← RuntimeOwnerMap.check [owner 0] actual.thenState [⟨owner 0,port 3⟩]
    pure () : WorkM Unit).run 200000 with
  | (.error .request,_) => true
  | _ => false)

end QleisliKernel.Tests.RuntimeOwnerPhis
