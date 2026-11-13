import QleisliKernel.Qirf.RuntimeScatterTransport

/-! Exact placement transport for the literal SWAP portion of a target schedule.
The ordered logical axes move with physical transpositions. The laws apply to
individual coefficients with an arbitrary external reference and preserve phase.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.Routing
open Semantics.Finite
open Qirf.RuntimeScatterTransport (write bit_write bit_lt scatter_at scatter_outside gather_at)

structure Swap where
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

def Swap.axis (move : Swap) (index : Nat) : Nat :=
  if index = move.first then move.second else if index = move.second then move.first else index

theorem Swap.axis_involutive (move : Swap) (index : Nat) : move.axis (move.axis index) = index := by
  rcases move with ⟨first,second⟩
  by_cases same : first = second
  · subst second
    by_cases hit : index = first <;> simp [Swap.axis,hit]
  by_cases hf : index = first
  · subst index
    simp [Swap.axis,Ne.symm same]
  by_cases hs : index = second
  · subst index
    simp [Swap.axis,Ne.symm same]
  simp [Swap.axis,hf,hs]

/-- Basis action of the emitted two-wire SWAP. Both new bits are read from the
original label. Each coefficient retains its original scalar, including phase. -/
def Swap.label (move : Swap) (input : Nat) : Nat :=
  write (write input move.first (bit input move.second)) move.second (bit input move.first)

theorem Swap.label_bit (move : Swap) (input index : Nat) :
    bit (move.label input) index = bit input (move.axis index) := by
  rcases move with ⟨first,second⟩
  simp only [Swap.label,Swap.axis,bit_write _ _ _ _ (bit_lt _ _)]
  by_cases hf : index = first <;> by_cases hs : index = second <;> simp only [hf,hs,ite_true,ite_false]
  · simp [hf.symm.trans hs]
  · have different : first ≠ second := fun equal => hs (hf.trans equal)
    rw [if_neg different]
  · have different : second ≠ first := fun equal => hf (hs.trans equal)
    rw [if_neg different]

private theorem bit_ext (left right : Nat) (same : ∀ index,bit left index = bit right index) : left = right := by
  apply Nat.eq_of_testBit_eq
  intro index
  have equal := same index
  simp only [bit] at equal
  rw [← Nat.toNat_testBit left index,← Nat.toNat_testBit right index] at equal
  cases leftBit : left.testBit index <;> cases rightBit : right.testBit index <;> simp_all

private theorem Swap.map_nodup (move : Swap) {axes : List Nat} (unique : axes.Nodup) :
    (axes.map move.axis).Nodup :=
  List.Pairwise.map _ (fun {left right} different equal =>
    different (by simpa only [move.axis_involutive] using congrArg move.axis equal)) unique

theorem Swap.scatter_placed (move : Swap) (base value : Nat) (axes : List Nat) (unique : axes.Nodup) :
    move.label (scatter base axes value) = scatter (move.label base) (axes.map move.axis) value := by
  have mappedUnique := move.map_nodup unique
  apply bit_ext
  intro index
  rw [move.label_bit]
  by_cases chosen : move.axis index ∈ axes
  · obtain ⟨position,bound,hits⟩ := List.getElem_of_mem chosen
    have mappedBound : position < (axes.map move.axis).length := by simpa only [List.length_map] using bound
    have mapped : (axes.map move.axis)[position]'mappedBound = index := by
      simp only [List.getElem_map,hits,move.axis_involutive]
    have first := scatter_at base value axes unique position bound
    have next := scatter_at (move.label base) value (axes.map move.axis) mappedUnique position mappedBound
    rw [hits] at first
    rw [mapped] at next
    rw [first,next]
  · have outside : index ∉ axes.map move.axis := by
      intro member
      obtain ⟨original,present,equal⟩ := List.mem_map.mp member
      have same : original = move.axis index := by simpa only [move.axis_involutive] using congrArg move.axis equal
      exact chosen (same ▸ present)
    rw [scatter_outside _ _ _ _ chosen,scatter_outside _ _ _ _ outside,move.label_bit]

def placement (moves : List Swap) (axes : List Nat) : List Nat :=
  moves.foldl (fun current move => current.map move.axis) axes

def basisAction (moves : List Swap) (input : Nat) : Nat :=
  moves.foldl (fun label move => move.label label) input

theorem Swap.gather_placed (move : Swap) (axes : List Nat) (input : Nat) :
    gather (move.label input) (axes.map move.axis) = gather input axes := by
  unfold gather
  rw [FiniteRestriction.zipIdx_map,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  simp [move.label_bit,move.axis_involutive]

/-- Physical SWAPs compose in the emitted order. Reading at the final
placement recovers the original value in the original logical axis order. -/
theorem gather_placed (moves : List Swap) (axes : List Nat) (input : Nat) :
    gather (basisAction moves input) (placement moves axes) = gather input axes := by
  induction moves generalizing axes input with
  | nil => rfl
  | cons move rest ih =>
    exact (ih (axes.map move.axis) (move.label input)).trans (move.gather_placed axes input)

/-- Exact routing commutes with placement of any local register and arbitrary
spectator label. A zero-width or reversed register uses the same law. -/
theorem scatter_placed (moves : List Swap) (base value : Nat) (axes : List Nat) (unique : axes.Nodup) :
    basisAction moves (scatter base axes value) = scatter (basisAction moves base) (placement moves axes) value := by
  induction moves generalizing base axes with
  | nil => rfl
  | cons move rest ih =>
    have mappedUnique := move.map_nodup unique
    change basisAction rest (move.label (scatter base axes value)) =
      scatter (basisAction rest (move.label base)) (placement rest (axes.map move.axis)) value
    rw [move.scatter_placed base value axes unique,ih _ _ mappedUnique]

theorem placement_length (moves : List Swap) (axes : List Nat) :
    (placement moves axes).length = axes.length := by
  induction moves generalizing axes with
  | nil => rfl
  | cons move rest ih =>
    exact (ih (axes.map move.axis)).trans (List.length_map _)

theorem placement_unique (moves : List Swap) (axes : List Nat) (unique : axes.Nodup) :
    (placement moves axes).Nodup := by
  induction moves generalizing axes with
  | nil => exact unique
  | cons move rest ih => exact ih _ (move.map_nodup unique)

/-- The target's two-operand gate uses the same zero-phase monomial as the
terminal emitter. The ordered axes are the literal physical operands. -/
def Swap.step (move : Swap) : Step := ⟨[],.monomial [move.first,move.second] [0,2,1,3] [0,0,0,0]⟩

theorem Swap.gather_two (move : Swap) (input : Nat) :
    gather input [move.first,move.second] = bit input move.first + 2*bit input move.second := by
  simp [gather,List.zipIdx_cons,Nat.mul_comm]

theorem Swap.scatter_label (move : Swap) (input : Nat) (distinct : move.first ≠ move.second) :
    scatter input [move.first,move.second] (gather input [move.second,move.first]) = move.label input := by
  have unique : [move.first,move.second].Nodup := by simp [distinct]
  apply bit_ext
  intro index
  by_cases first : index = move.first
  · subst index
    have written := scatter_at input (gather input [move.second,move.first]) _ unique 0 (by simp)
    change bit (scatter input [move.first,move.second] (gather input [move.second,move.first])) move.first = _ at written
    have read := gather_at input [move.second,move.first] 0 (by simp)
    rw [written,read,move.label_bit]
    simp [Swap.axis]
  by_cases second : index = move.second
  · subst index
    have written := scatter_at input (gather input [move.second,move.first]) _ unique 1 (by simp)
    change bit (scatter input [move.first,move.second] (gather input [move.second,move.first])) move.second = _ at written
    have read := gather_at input [move.second,move.first] 1 (by simp)
    rw [written,read,move.label_bit]
    simp [Swap.axis,Ne.symm distinct]
  have outside : index ∉ [move.first,move.second] := by simp [first,second]
  rw [scatter_outside _ _ _ _ outside,move.label_bit]
  simp [Swap.axis,first,second]

private theorem swapTable (a b : Nat) (ha : a < 2) (hb : b < 2) :
    ([0,2,1,3] : List Nat)[a+2*b]? = some (b+2*a) := by
  have ca : a = 0 ∨ a = 1 := by omega
  have cb : b = 0 ∨ b = 1 := by omega
  rcases ca with rfl | rfl <;> rcases cb with rfl | rfl <;> rfl

private theorem zeroTable (a b : Nat) (ha : a < 2) (hb : b < 2) :
    ([0,0,0,0] : List Nat)[a+2*b]? = some 0 := by
  have ca : a = 0 ∨ a = 1 := by omega
  have cb : b = 0 ∨ b = 1 := by omega
  rcases ca with rfl | rfl <;> rcases cb with rfl | rfl <;> rfl

/-- Independent executable finite action of the actual gate. A nonzero
amplitude at any input label contributes the identical scalar at its routed
label. No global matrix or state is enumerated. -/
theorem Swap.contribution (move : Swap) (input : Nat) (value : Semantics.Exact.Scalar)
    (distinct : move.first ≠ move.second) (valid : QleisliKernel.Exact.Scalar.valid value = true) :
    Finite.contributions [] move.step input value =
      .ok (if value == Semantics.Exact.Scalar.zero then [] else [(move.label input,value)]) := by
  by_cases zero : (value == Semantics.Exact.Scalar.zero) = true
  · simp [Finite.contributions,zero,pure,Except.pure]
  · have permuted := swapTable (bit input move.first) (bit input move.second) (bit_lt _ _) (bit_lt _ _)
    have phases := zeroTable (bit input move.first) (bit input move.second) (bit_lt _ _) (bit_lt _ _)
    have phaseZero : QleisliKernel.Exact.Scalar.phase 0 = Semantics.Exact.Scalar.one := rfl
    have swapped : gather input [move.second,move.first] = bit input move.second + 2*bit input move.first :=
      (Swap.mk move.second move.first).gather_two input
    simp only [Finite.contributions,Swap.step,zero,enabled,List.all_nil,Bool.not_true]
    simp [move.gather_two,permuted,phases,Finite.readOption,← swapped]
    change (do
      let scaled ← Finite.arithmetic (QleisliKernel.Exact.Scalar.mul value (QleisliKernel.Exact.Scalar.phase 0))
      pure [(scatter input [move.first,move.second] (gather input [move.second,move.first]),scaled)]) = _
    rw [phaseZero,QleisliKernel.Exact.scalar_mul_one value valid,move.scatter_label input distinct]
    rfl

theorem Swap.label_involutive (move : Swap) (input : Nat) : move.label (move.label input) = input := by
  apply bit_ext
  intro index
  rw [move.label_bit,move.label_bit,move.axis_involutive]

def coefficients {Reference Scalar : Type} (moves : List Swap)
    (input : Reference → Nat → Scalar) : Reference → Nat → Scalar :=
  fun reference output => input reference (basisAction moves.reverse output)

theorem basisAction_reverse (moves : List Swap) (input : Nat) :
    basisAction moves.reverse (basisAction moves input) = input := by
  induction moves generalizing input with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.reverse_cons,basisAction,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [show List.foldl (fun label move => Swap.label move label)
      (List.foldl (fun label move => Swap.label move label) (first.label input) rest) rest.reverse =
      first.label input from ih (first.label input), first.label_involutive]

/-- The actual reference index and scalar travel unchanged along the literal
physical basis permutation. No separability or phase quotient is needed. -/
theorem coefficients_placed {Reference Scalar : Type} (moves : List Swap)
    (input : Reference → Nat → Scalar) (reference : Reference) (label : Nat) :
    coefficients moves input reference (basisAction moves label) = input reference label := by
  rw [coefficients,basisAction_reverse]

theorem pull_routed {Reference Scalar : Type} (moves : List Swap)
    (input : Reference → Nat → Scalar) (reference : Reference)
    (base value : Nat) (axes : List Nat) (unique : axes.Nodup) :
    coefficients moves input reference (scatter (basisAction moves base) (placement moves axes) value) =
      input reference (scatter base axes value) := by
  rw [← scatter_placed moves base value axes unique,coefficients_placed]

/-- Fixed-occupancy part of an abstract target profile. Every occupied axis
is reserved before routing, including source, synthesis and routing scratch.
The caller must establish the meaning of the target's literal SWAP instruction. -/
structure Profile where
  capacity : Nat
  connected : Nat → Nat → Bool

private def legal (profile : Profile) (occupied : List Nat) (move : Swap) : Bool :=
  move.first != move.second && occupied.contains move.first && occupied.contains move.second &&
    profile.connected move.first move.second

structure Checked (profile : Profile) (occupied : List Nat) (moves : List Swap) where
  initialUnique : occupied.Nodup
  initialBounds : ∀ axis ∈ occupied,axis < profile.capacity
  admissible : ∀ move ∈ moves,legal profile occupied move = true
  final : List Nat
  placementRead : final = placement moves occupied

def check (profile : Profile) (occupied : List Nat) (moves : List Swap) :
    Option (Checked profile occupied moves) :=
  if unique : occupied.Nodup then
    if bounds : ∀ axis ∈ occupied,axis < profile.capacity then
      if allowed : moves.all (legal profile occupied) = true then
        some ⟨unique,bounds,List.all_eq_true.mp allowed,placement moves occupied,rfl⟩
      else none
    else none
  else none

theorem Swap.axis_mem (move : Swap) (axes : List Nat) (first : move.first ∈ axes)
    (second : move.second ∈ axes) (axis : Nat) (member : axis ∈ axes) : move.axis axis ∈ axes := by
  unfold Swap.axis
  split
  · exact second
  split
  · exact first
  · exact member

theorem Checked.finalBounds {profile occupied moves} (checked : Checked profile occupied moves)
    (axis : Nat) (member : axis ∈ checked.final) : axis < profile.capacity := by
  rw [checked.placementRead] at member
  have retains (rest : List Swap) (axes : List Nat) (subset : ∀ axis ∈ axes,axis ∈ occupied)
      (allowed : ∀ move ∈ rest,legal profile occupied move = true) :
      ∀ axis ∈ placement rest axes,axis ∈ occupied := by
    induction rest generalizing axes with
    | nil => exact subset
    | cons move rest ih =>
      have good := allowed move List.mem_cons_self
      simp only [legal,Bool.and_eq_true,List.contains_iff_mem] at good
      apply ih (axes.map move.axis)
      · intro axis found
        obtain ⟨original,member,rfl⟩ := List.mem_map.mp found
        exact move.axis_mem occupied good.1.1.2 good.1.2 original (subset original member)
      · exact fun item found => allowed item (List.mem_cons_of_mem move found)
  exact checked.initialBounds axis (retains moves occupied (fun _ found => found) checked.admissible axis member)

theorem Checked.finalUnique {profile occupied moves} (checked : Checked profile occupied moves) :
    checked.final.Nodup := by
  rw [checked.placementRead]
  exact placement_unique moves occupied checked.initialUnique

theorem Checked.finalWidth {profile occupied moves} (checked : Checked profile occupied moves) :
    checked.final.length = occupied.length := by
  rw [checked.placementRead,placement_length]

theorem Checked.preservesPlacement {profile occupied moves} (checked : Checked profile occupied moves)
    (label : Nat) : gather (basisAction moves label) checked.final = gather label occupied := by
  rw [checked.placementRead]
  exact gather_placed moves occupied label

private def readSwap (step : Step) : Option {move : Swap // move.step = step} :=
  match step with
  | ⟨[],.monomial [first,second] [0,2,1,3] [0,0,0,0]⟩ => some ⟨⟨first,second⟩,rfl⟩
  | _ => none

private def readSwaps : (steps : List Step) → Option {moves : List Swap // moves.map Swap.step = steps}
  | [] => some ⟨[],rfl⟩
  | step :: rest => do
    let move ← readSwap step
    let moves ← readSwaps rest
    return ⟨move.val :: moves.val,by simp [move.property,moves.property]⟩

theorem Checked.gateContribution {profile occupied moves} (checked : Checked profile occupied moves)
    (move : Swap) (member : move ∈ moves) (input : Nat) (value : Semantics.Exact.Scalar)
    (valid : QleisliKernel.Exact.Scalar.valid value = true) :
    Finite.contributions [] move.step input value =
      .ok (if value == Semantics.Exact.Scalar.zero then [] else [(move.label input,value)]) := by
  have admissible := checked.admissible move member
  simp only [legal,Bool.and_eq_true,bne_iff_ne] at admissible
  exact move.contribution input value admissible.1.1.1 valid

/-- The schedule retains the literal gate word and checks occupied physical
locations once. Charging every literal SWAP separately includes pairs that
cancel semantically. Connectivity and other physical conventions come from the
explicit target profile. This fixed-occupancy model has no allocation event. -/
structure Schedule (profile : Profile) (occupied : List Nat) (actual : List Step) where
  moves : List Swap
  original : moves.map Swap.step = actual
  checked : Checked profile occupied moves

def read (profile : Profile) (occupied : List Nat) (actual : List Step) :
    Option (Schedule profile occupied actual) := do
  let moves ← readSwaps actual
  let checked ← check profile occupied moves.val
  return ⟨moves.val,moves.property,checked⟩

def Schedule.swapCount {profile occupied actual} (schedule : Schedule profile occupied actual) : Nat :=
  schedule.moves.length

def Schedule.liveWidth {profile occupied actual} (_schedule : Schedule profile occupied actual) : Nat :=
  occupied.length

theorem Schedule.swapCount_original {profile occupied actual} (schedule : Schedule profile occupied actual) :
    schedule.swapCount = actual.length := by
  simpa only [Schedule.swapCount,List.length_map] using congrArg List.length schedule.original

theorem Schedule.width_during {profile occupied actual} (schedule : Schedule profile occupied actual)
    (length : Nat) : (placement (schedule.moves.take length) occupied).length = schedule.liveWidth :=
  placement_length _ _

theorem Schedule.actualGateContribution {profile occupied actual} (schedule : Schedule profile occupied actual)
    (step : Step) (member : step ∈ actual) :
    ∃ move ∈ schedule.moves,move.step = step ∧
      ∀ input value,QleisliKernel.Exact.Scalar.valid value = true →
        Finite.contributions [] step input value =
          .ok (if value == Semantics.Exact.Scalar.zero then [] else [(move.label input,value)]) := by
  rw [← schedule.original] at member
  obtain ⟨move,present,equal⟩ := List.mem_map.mp member
  refine ⟨move,present,equal,?_⟩
  rw [← equal]
  exact schedule.checked.gateContribution move present

theorem Schedule.preservesCoefficients {profile occupied actual} (schedule : Schedule profile occupied actual)
    {Reference Scalar : Type} (input : Reference → Nat → Scalar) (reference : Reference)
    (base value : Nat) :
    coefficients schedule.moves input reference (scatter (basisAction schedule.moves base) schedule.checked.final value) =
      input reference (scatter base occupied value) := by
  rw [schedule.checked.placementRead]
  exact pull_routed schedule.moves input reference base value occupied schedule.checked.initialUnique

private def line : Profile := ⟨3,fun a b => a+1 == b || b+1 == a⟩
private def first : Swap := ⟨0,1⟩
private def second : Swap := ⟨1,2⟩
#guard (read line [0,1,2] [first.step,second.step]).map
  (fun schedule => (schedule.checked.final,schedule.swapCount)) == some ([2,0,1],2)
#guard (read line [0,1,2] [first.step,first.step]).map
  (fun schedule => (schedule.checked.final,schedule.swapCount)) == some ([0,1,2],2)
#guard (read line [0,1,2] [(Swap.mk 0 2).step]).isNone
#guard (read line [0,1] [second.step]).isNone
#guard (read line [0,1,3] [first.step]).isNone
#guard (read line [0,0,1] [first.step]).isNone
#guard (read line [0,1,2] [⟨[],.monomial [0,1] [0,2,1,3] [4,4,4,4]⟩]).isNone
#guard (read line [] []).map (fun schedule => schedule.swapCount) == some 0

end QleisliKernel.Target.Routing
