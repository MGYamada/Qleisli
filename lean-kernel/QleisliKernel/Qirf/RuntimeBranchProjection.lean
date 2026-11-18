import QleisliKernel.Qirf.RuntimeCallScope
import QleisliKernel.Qirf.RuntimeOwnerPhis

/-! Derive the selected part of one actual ordinary Raw branch. Both original
arms and all phis remain checked by the full parent interval. A parked owner
has its own literal phi and retains its logical identity across either arm.
Original named-body and history correspondence are separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBranchProjection
open QleisliKernel Finite SourceTypes RuntimeOwnerMap
abbrev Port := Semantics.Raw.Port
abbrev Phi := Semantics.Observation.QuantumPhi

private def parked (entry : Map) (inputs : List Nat) : Map :=
  entry.filter (fun binding => !inputs.contains binding.port.token)

private def parkedPhi (spectators : Map) (phi : Phi) : Bool :=
  spectators.any (fun binding => binding.port.token == phi.thenToken || binding.port.token == phi.elseToken)

structure Move (spectators : Map) (phi : Phi) where
  original : RuntimeOwnerPhis.One [] (spectators.map (·.owner)) spectators spectators phi
  same : original.thenBinding = original.elseBinding
  retained : original.sourceIndex = none

private theorem spectatorRole {spectators left right index out}
    (role : RuntimeOwnerPhis.Role [] spectators left right index out) :
    index = none ∧ out = left := by
  cases role with
  | selected _ _ impossible _ _ => simp at impossible
  | spectator _ _ => exact ⟨rfl,rfl⟩

theorem Move.owner {spectators phi} (move : Move spectators phi) :
    move.original.binding.owner = move.original.thenBinding.owner :=
  (spectatorRole move.original.role).2

private def readMove (spectators : Map) (phi : Phi) : WorkM (Move spectators phi) := do
  let one ← RuntimeOwnerPhis.readOne [] (spectators.map (·.owner)) spectators spectators phi
  if same : one.thenBinding = one.elseBinding then
    return ⟨one,same,(spectatorRole one.role).1⟩
  else throw .request

def program {dependencies original block offset} (branch : @RuntimeInterval.Branch dependencies original block offset)
    (selected : List Port) (spectators : Map) (classicalInputs : List Nat) : Semantics.Observation.Program :=
  let phis := branch.quantum.filter (fun phi => !parkedPhi spectators phi)
  RuntimeCallScope.program selected classicalInputs
    [.branch branch.condition branch.thenOps branch.elseOps phis branch.classical]
    (phis.map (·.output)) (RuntimeOrdinaryBody.visibleIds branch.interval.after) .unitary

structure Checked {dependencies original block offset roles}
    (branch : @RuntimeInterval.Branch dependencies original block offset)
    (entry : RuntimeOwnerMap.Checked roles branch.interval.before)
    (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State) where
  selected : List Port
  atEntry : PureInterval.ports branch.interval.before inputs = some selected
  visible : RuntimeOrdinaryBody.Visible branch.interval.before ordinary
  thenParked : PureInterval.ports branch.thenState ((parked entry.bindings inputs).map (·.port.token)) =
    some ((parked entry.bindings inputs).map (·.port))
  elseParked : PureInterval.ports branch.elseState ((parked entry.bindings inputs).map (·.port.token)) =
    some ((parked entry.bindings inputs).map (·.port))
  moves : List ((phi : Phi) × Move (parked entry.bindings inputs) phi)
  allMoves : moves.map Sigma.fst = branch.quantum.filter (parkedPhi (parked entry.bindings inputs))
  completeEntry : (selected ++ moves.map (·.2.original.thenBinding.port)).Perm branch.interval.before.quantum.live
  prepared : RuntimeInterval.Prepared dependencies
    (program branch selected (parked entry.bindings inputs) (visible.table.map Prod.fst))
  completeExit : (prepared.whole.state.quantum.live ++ moves.map (·.2.original.binding.port)).Perm
    branch.interval.after.quantum.live

def Checked.program {dependencies original block offset roles branch entry inputs ordinary}
    (checked : @Checked dependencies original block offset roles branch entry inputs ordinary) :
    Semantics.Observation.Program :=
  RuntimeBranchProjection.program branch checked.selected (parked entry.bindings inputs) (checked.visible.table.map Prod.fst)

def Checked.renames {dependencies original block offset roles branch entry inputs ordinary}
    (checked : @Checked dependencies original block offset roles branch entry inputs ordinary) : List (Nat × Nat) :=
  checked.moves.map (fun move => (move.2.original.thenBinding.port.token,move.1.output))

/-- Project the fixed literal branch. Neither the condition nor either arm
can come from a proposed local program. The two complete Raw interfaces are
checked independently, and their actual output ports must partition exactly. -/
def read {dependencies original block offset roles}
    (branch : @RuntimeInterval.Branch dependencies original block offset)
    (entry : RuntimeOwnerMap.Checked roles branch.interval.before)
    (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State) : WorkM (Checked branch entry inputs ordinary) := do
  guard (inputs.length ≤ 64 && entry.bindings.length ≤ 128 && branch.quantum.length ≤ 128) .limit
  let fields := Raw.OwnerFlow.fields roles+
    (entry.bindings.map fun b => b.port.token.log2/8+b.port.wires.length+1).sum+
    (branch.quantum.map fun p => p.thenToken.log2/8+p.elseToken.log2/8+p.output.log2/8+p.wires.length+1).sum
  exactWork (Exact.charge (32*(fields+1)*(inputs.length+entry.bindings.length+branch.quantum.length+1)^2))
  guard (decide inputs.Nodup) .request
  match atEntry : PureInterval.ports branch.interval.before inputs with
  | none => throw .request
  | some selected =>
    let spectators := parked entry.bindings inputs
    let tokens := spectators.map (·.port.token)
    let ports := spectators.map (·.port)
    if parkedInArms : PureInterval.ports branch.thenState tokens = some ports ∧
        PureInterval.ports branch.elseState tokens = some ports then
      let moves ← (branch.quantum.filter (parkedPhi spectators)).mapM fun phi => do
        return (⟨phi,← readMove spectators phi⟩ : (phi : Phi) × Move spectators phi)
      if coverage : moves.map Sigma.fst = branch.quantum.filter (parkedPhi spectators) ∧
          (selected ++ moves.map (·.2.original.thenBinding.port)).Perm branch.interval.before.quantum.live then
        let visible ← RuntimeOrdinaryBody.readVisible branch.interval.before ordinary
        let prepared ← RuntimeInterval.prepare dependencies
          (program branch selected spectators (visible.table.map Prod.fst))
        if complete : (prepared.whole.state.quantum.live ++ moves.map (·.2.original.binding.port)).Perm
            branch.interval.after.quantum.live then
          return ⟨selected,atEntry,visible,parkedInArms.1,parkedInArms.2,moves,coverage.1,coverage.2,prepared,complete⟩
        else throw .request
      else throw .request
    else throw .request

end QleisliKernel.Qirf.RuntimeBranchProjection
