import QleisliKernel.Qirf.RuntimePureInterval

/-! Small literal mixed-runtime interval controls. No native handle or
source-preservation claim is obtained from these component checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeInterval
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf.RuntimeInterval

private def program (rightId : Nat := 11) : Program :=
  ⟨[⟨0,[],0⟩,⟨1,[0],1⟩],[],
    [.constant true 9,
      .branch 9 [.measure 1 10] [.discard 1,.constant false rightId]
        [⟨0,0,2,[]⟩] [⟨10,rightId,12⟩]],
    [2],[12],.observe⟩

private def retained : WorkM Bool := do
  let prepared ← prepare [] (program 11)
  let branch ← readBranch prepared.block 1
  let left ← check branch.thenBlock 0 1
  let right ← check branch.elseBlock 0 2
  return branch.condition == 9 &&
    branch.thenBlock.operations.length == 1 && branch.elseBlock.operations.length == 2 &&
    left.after.observe && right.after.observe &&
    right.after.quantum.live.map (·.token) == [0] &&
    branch.interval.after.quantum.live.map (·.token) == [2] &&
    branch.interval.after.quantum.live.flatMap (·.wires) == [] &&
    right.after.classical.any (fun (id,_) => id == 10) &&
    !right.after.active.contains branch.thenBlock.entry.scope &&
    branch.thenBlock.entry.scope != branch.elseBlock.entry.scope

#guard (retained.run 200000).1.toOption = some true

-- A known-true condition does not permit its inactive arm to redefine the
-- measured SSA identity issued by the first original arm.
#guard (match (prepare [] (program 10)).run 200000 with
  | (.error _,_) => true
  | _ => false)

#guard (match (do
    let prepared ← prepare [] (program 11)
    let _ ← check prepared.block 2 1
    pure () : WorkM Unit).run 200000 with
  | (.error .request,_) => true
  | _ => false)

private def nestedPure : Program :=
  ⟨[⟨0,[],0⟩,⟨1,[0],1⟩],[],
    [.constant true 9,
      .branch 9 [.pure (.gate .h 1 3),.measure 3 10] [.discard 1,.constant false 11]
        [⟨0,0,2,[]⟩] [⟨10,11,12⟩]],
    [2],[12],.observe⟩

private def localPure : WorkM Bool := do
  let prepared ← prepare [] nestedPure
  let branch ← readBranch prepared.block 1
  let action ← Qirf.RuntimePureInterval.check branch.thenBlock 1 0 1 [1] [3] [⟨7,[.bit]⟩]
  -- Identity on a separate zero-width owner has an empty actual interval.
  let identity ← Qirf.RuntimePureInterval.check branch.thenBlock 1 0 0 [0] [0] [⟨8,[.unit]⟩]
  return action.selected.map (·.token) == [1] && action.returned.map (·.token) == [3] &&
    identity.selected.map (·.token) == [0] && identity.operations.isEmpty &&
    action.interval.after.quantum.live.any (fun port => port.token == 0 && port.wires.isEmpty)

#guard (localPure.run 200000).1.toOption = some true

-- A genuine observation remains in the mixed block and cannot be admitted as
-- a pure local action merely because the surrounding result is a zero owner.
#guard (match (do
    let prepared ← prepare [] nestedPure
    let branch ← readBranch prepared.block 1
    let _ ← Qirf.RuntimePureInterval.check branch.thenBlock 1 1 1 [3] [3] [⟨7,[.bit]⟩]
    pure () : WorkM Unit).run 200000 with
  | (.error .request,_) => true
  | _ => false)

#guard (match (do
    let prepared ← prepare [] (program 11)
    let _ ← readBranch prepared.block 0
    pure () : WorkM Unit).run 200000 with
  | (.error .request,_) => true
  | _ => false)

end QleisliKernel.Tests.RuntimeInterval
