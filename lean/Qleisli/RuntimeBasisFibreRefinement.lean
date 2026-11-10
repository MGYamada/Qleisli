import Qleisli.RuntimeBasisSourceAction
import Qleisli.RuntimeCallTraceBasis

/-! Original rectangular basis actions lift to an arbitrary spectator and
reference space by the same sparse code on the actual physical wires.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeBasisFibreRefinement
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather)
open RuntimeOwnerMap (Binding Map)
open RuntimeSemanticForest (Frame ownerLayout product)
open RuntimeBasisSourceAction (encodeDigit logicalRow encode_row applyRow fibre_applyRow encoded_block)
open RuntimeNamedHeadCoefficients (fibre)
open RuntimeForestCode (forestAxes sparseEntry)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.Semantics.RawAction (event)

private noncomputable def spectatorWeight (spectators : Map) (coordinate digit : Nat) : ℂ :=
  scalar (sparseEntry (.ofLayout (product spectators)) coordinate digit)

/-- The literal physical operation on the complete input encoding equals
the original logical table on every correlated spectator fibre. -/
theorem encoded_fibre {before after : Binding} {spectators : Map}
    {rows : List (List Nat)} {table row : List Nat}
    (input : Frame (before :: spectators)) (output : Frame (after :: spectators))
    (tableCheck : RuntimeBasisAction.rowsMatch (ownerLayout before) (ownerLayout after) rows table = true)
    (rowPresent : row ∈ rows)
    (dependencies : List Semantics.Finite.Dependency) (prior next extra : List Nat)
    (priorUnique : prior.Nodup) (nextUnique : next.Nodup)
    (priorPerm : prior.Perm (before.port.wires ++ spectators.flatMap (·.port.wires)))
    (nextPerm : next.Perm (after.port.wires ++ spectators.flatMap (·.port.wires)))
    (growth : next = prior ++ extra) (localGrowth : after.port.wires = before.port.wires ++ extra)
    (tableBound : ∀ index : Nat, table[index]?.getD 0 < 2^after.port.wires.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference)
    (physicalBound : physical < 2^next.length) :
    event dependencies (.liftBasis prior.length next.length
        (before.port.wires.map prior.idxOf) (after.port.wires.map next.idxOf) table)
      (fun index => RuntimeSemanticForest.action input prior joint index reference) physical =
    RuntimeSemanticForest.action output next
      (applyRow row (ownerLayout after).labels.length joint) physical reference := by
  let others := spectators.flatMap (fun binding => binding.port.wires)
  let width := (ownerLayout before).labels.length
  let outputWidth := (ownerLayout after).labels.length
  let spectatorCount := (product spectators).labels.length
  let jointEncoded := fun index high => encodeDigit (ownerLayout before)
    (fun digit => fibre width spectatorCount (spectatorWeight spectators high) joint digit reference) index
  let high := gather physical (others.map next.idxOf)
  let low := gather physical (after.port.wires.map next.idxOf)
  have inputWidth : before.port.wires.length = (ownerLayout before).bits :=
    (RuntimeSemanticForest.owner_layout (input.available before List.mem_cons_self)).2
  have inputCode : Semantics.FiniteCarrier.layout before.owner.basis = some (ownerLayout before) :=
    (RuntimeSemanticForest.owner_layout (input.available before List.mem_cons_self)).1
  have rowSize := beq_iff_eq.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp tableCheck).2 row rowPresent)).1
  have inputEncoded (index : Nat) : RuntimeSemanticForest.action input prior joint index reference =
      jointEncoded (gather index (before.port.wires.map prior.idxOf)) (gather index (others.map prior.idxOf)) :=
    encoded_block input prior joint index reference
  simp only [inputEncoded]
  rw [RuntimeCallTraceBasis.basis_event_fibre dependencies prior before.port.wires others next after.port.wires extra
    table priorPerm nextPerm priorUnique nextUnique growth localGrowth tableBound jointEncoded physical physicalBound]
  change ((List.range (2^before.port.wires.length)).map fun index =>
    if table[index]?.getD 0 = low then jointEncoded index high else 0).sum = _
  rw [inputWidth]
  change ((List.range (2^(ownerLayout before).bits)).map fun index =>
    if table[index]?.getD 0 = low then encodeDigit (ownerLayout before)
      (fun digit => fibre width spectatorCount (spectatorWeight spectators high) joint digit reference) index else 0).sum = _
  rw [encode_row tableCheck rowPresent (RuntimeForestProduct.layout_bounds _ _ inputCode).2]
  rw [encoded_block output next (applyRow row outputWidth joint) physical reference]
  unfold encodeDigit
  apply Qleisli.Exact.sum_map_congr
  intro digit member
  have bound := List.mem_range.mp member
  have entry := fibre_applyRow row outputWidth spectatorCount (spectatorWeight spectators high) joint digit reference bound
  rw [rowSize] at entry
  change (if (ownerLayout after).labels[digit]? = some low then
      logicalRow row (fun input => fibre (ownerLayout before).labels.length spectatorCount
        (spectatorWeight spectators high) joint input reference) digit else 0) =
    (if (ownerLayout after).labels[digit]? = some low then
      fibre outputWidth spectatorCount (spectatorWeight spectators high)
        (applyRow row outputWidth joint) digit reference else 0)
  rw [entry]

#print axioms encoded_fibre
end Qleisli.RuntimeBasisFibreRefinement
