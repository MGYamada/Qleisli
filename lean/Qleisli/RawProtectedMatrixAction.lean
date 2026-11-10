import Qleisli.RawReconstructedAction
import Qleisli.RawFiniteRows
import Qleisli.RawEventLinear

/-! The matrix reconstructed for a protected scope has the independent
literal action on arbitrary complex amplitudes. The finite target domain
is justified by the scope's actual use validation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.ReconstructedAction
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Event Gate Use)
open Qleisli.Semantics.Exact Qleisli.Semantics.Protected
open Qleisli.Semantics.RawAction (combination protected_blocks_combination)

private theorem gate_on_rows (bits axis : Nat) (bounded : axis < bits) (operation : Gate)
    (left right : Nat → ℂ) (same : RawFiniteRows.OnRows bits left right) :
    RawFiniteRows.OnRows bits (gate operation axis left) (gate operation axis right) := by
  intro row inside
  cases operation with
  | x =>
    exact same _ (Nat.xor_lt_two_pow inside (Nat.pow_lt_pow_right (by decide) bounded))
  | z | t => simp only [gate,same row inside]
  | h =>
    let step : Step := ⟨[],.hadamard axis⟩
    have geometry : RawFiniteRows.BoundedEvent bits (.circuit bits [step]) bits := by
      apply RawFiniteRows.BoundedEvent.circuit
      intro op member target held
      have equal : op = step := List.mem_singleton.mp member
      subst op
      have sameAxis : target = axis := List.mem_singleton.mp held
      exact sameAxis.symm ▸ bounded
    exact geometry.congr [] left right same row inside

private theorem blocks_on_rows (sourceBits ancillaBits bits source ancilla : Nat)
    (uses : List Use) (valid : Raw.usesValid sourceBits ancillaBits bits uses = true)
    {Reference : Type} (left right : Nat → Reference → ℂ)
    (same : ∀ reference, RawFiniteRows.OnRows bits (fun row => left row reference) (fun row => right row reference)) :
    ∀ reference, RawFiniteRows.OnRows bits (fun row => blocks source ancilla uses left row reference)
      (fun row => blocks source ancilla uses right row reference) := by
  induction uses generalizing left right with
  | nil => exact same
  | cons use rest ih =>
    have headValid := List.all_eq_true.mp valid use List.mem_cons_self
    have tailValid : Raw.usesValid sourceBits ancillaBits bits rest = true :=
      List.all_eq_true.mpr (fun op member => List.all_eq_true.mp valid op (List.mem_cons_of_mem _ member))
    unfold blocks
    simp only [List.foldl_cons]
    apply ih tailValid _ _
    intro reference row inside
    cases use with
    | protectedGate location operation => simp only [blockUse,same reference row inside]
    | phase controls operation => simp only [blockUse,same reference row inside]
    | targetGate controls axis operation =>
      change (decide (axis < bits) && Raw.protectedControlsValid sourceBits ancillaBits controls) = true at headValid
      simp only [Bool.and_eq_true,decide_eq_true_eq] at headValid
      by_cases enabled : Semantics.Protected.enabled source ancilla controls = true
      · simpa only [blockUse,enabled,if_true] using
          gate_on_rows bits axis headValid.1 operation _ _ (same reference) row inside
      · simpa only [blockUse,enabled,if_false] using same reference row inside

#print axioms blocks_on_rows

private theorem scope_action {sourceBits dataBits ancillaBits : Nat}
    {function : List Nat} {uses : List Use} {actual : Matrix} (work left : Nat)
    (read : (Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function uses).run work =
      (.ok actual,left))
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < 2^dataBits) :
    action actual joint row reference =
      let f := fun source => function[source]?.getD 0
      let input : Logical Unit := fun source target _ => joint (source+target*2^sourceBits) reference
      let physical := compute f (run uses (compute f (zero input)))
      physical (row % 2^sourceBits) 0 (row / 2^sourceBits) () := by
  obtain ⟨_,middle,limited,remaining⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,guarded,_⟩ := bind_success _ _ _ _ _ remaining
  have limited := (guard_success _ _ _ _ limited).1
  have checked := (guard_success _ _ _ _ guarded).1
  simp only [Bool.and_eq_true,decide_eq_true_eq] at limited checked
  have sourceLe : sourceBits ≤ dataBits := limited.1.1
  have valid : Raw.usesValid sourceBits ancillaBits (dataBits-sourceBits) uses = true := checked.2
  have diagonal := Qleisli.Raw.uses_valid_diagonal _ _ _ _ valid
  obtain ⟨_,columns,_⟩ := Qleisli.Raw.ProtectedEvaluation.matrix_meaning _ _ _ _ _ _ _ _ read
  let f := fun (source : Nat) => function[source]?.getD 0
  let source := row % 2^sourceBits
  let target := row / 2^sourceBits
  let weight := fun col => joint col reference
  let basis := fun (col digit : Nat) (_ : Unit) =>
    Qleisli.Semantics.ProtectedMatrix.basis sourceBits col source digit ()
  let input := fun (digit : Nat) (_ : Unit) => joint (source+digit*2^sourceBits) reference
  let expanded := fun (digit : Nat) (ref : Unit) =>
    combination (List.range (2^dataBits)) weight (fun col => basis col digit ref)
  have sourceBound : source < 2^sourceBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have factor : 2^dataBits = 2^(dataBits-sourceBits)*2^sourceBits := by
    rw [← Nat.pow_add,Nat.sub_add_cancel sourceLe]
  have targetBound : target < 2^(dataBits-sourceBits) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (factor ▸ bounded)
  have coordinates (digit col : Nat) :
      (source = col % 2^sourceBits ∧ digit = col / 2^sourceBits) ↔ source+digit*2^sourceBits = col := by
    constructor
    · rintro ⟨low,high⟩
      rw [low,high,Nat.mod_add_div']
    · intro packed
      subst col
      constructor
      · rw [Nat.add_comm,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt sourceBound]
      · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt sourceBound,Nat.zero_add]
  have same : ∀ ref, RawFiniteRows.OnRows (dataBits-sourceBits)
      (fun digit => expanded digit ref) (fun digit => input digit ref) := by
    intro ref digit inside
    have scaled : (digit+1)*2^sourceBits ≤ 2^dataBits := by
      rw [factor]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul,Nat.one_mul] at scaled
    have packedBound : source+digit*2^sourceBits < 2^dataBits := by omega
    unfold expanded combination basis input Qleisli.Semantics.ProtectedMatrix.basis
    calc
      _ = ((List.range (2^dataBits)).map (fun col =>
          if source+digit*2^sourceBits = col then weight col else 0)).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro col _
        simp only [Bool.and_eq_true,beq_iff_eq,coordinates]
        split <;> simp
      _ = _ := Qleisli.Exact.range_delta_sum _ _ _ packedBound
  have entryAction (col : Nat) (inside : col < 2^dataBits) :
      entry actual row col = blocks source (f source) uses (basis col) target () := by
    rw [protected_matrix_entry work left read row col bounded inside]
    unfold Qleisli.Semantics.ProtectedMatrix.coefficient
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt inside]
    rw [Nat.add_comm (row*(2^dataBits)) col,Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt inside,Nat.zero_add]
    exact congrArg (fun family : Physical Unit => family source 0 target ())
      (clean_factorization f uses diagonal (Qleisli.Semantics.ProtectedMatrix.basis sourceBits col))
  change _ = compute f (run uses (compute f (zero (fun s t (_ : Unit) =>
    joint (s+t*2^sourceBits) reference)))) source 0 target ()
  rw [clean_factorization _ _ diagonal]
  change _ = blocks source (f source) uses input target ()
  calc
    _ = combination (List.range (2^dataBits)) weight
        (fun col => blocks source (f source) uses (basis col) target ()) := by
      unfold action combination
      rw [columns]
      apply Qleisli.Exact.sum_map_congr
      intro col member
      dsimp only [weight]
      rw [entryAction col (List.mem_range.mp member)]
    _ = blocks source (f source) uses expanded target () :=
      (congrFun (congrFun (protected_blocks_combination _ weight uses diagonal source (f source) basis) target) ()).symm
    _ = _ := blocks_on_rows sourceBits ancillaBits _ source (f source) uses valid
      expanded input same () target targetBound

/-- The checked protected block preserves the exact physical phase and
acts on the same selected fibre of every reference column. -/
theorem protected_event_action (dependencies : List Dependency) (bits : Nat) (axes : List Nat)
    (sourceBits ancillaBits : Nat) (function : List Nat) (uses : List Use)
    (actual : Matrix) (work left : Nat)
    (read : (Raw.ProtectedEvaluation.eventMatrix dependencies
      (.protectedComputed bits axes sourceBits ancillaBits function uses)).run work = (.ok actual,left)) :
    EventAction dependencies (.protectedComputed bits axes sourceBits ancillaBits function uses) actual := by
  intro Reference joint row reference bound
  obtain ⟨_,middle,_,remaining⟩ := bind_success _ _ _ _ _ read
  obtain ⟨logical,after,localRead,promote⟩ := bind_success _ _ _ _ _ remaining
  rw [promoted_action after left promote joint row reference bound]
  exact scope_action middle after localRead (fun col ref => joint (scatter row axes col) ref)
    (gather row axes) reference (Qleisli.RuntimeForestProduct.gather_bound row axes)

#print axioms protected_event_action

/-- Every physical event produced by the protected reconstruction has its
literal action on the checked finite output, including both computed forms. -/
theorem event_action (dependencies : List Dependency) (operation : Event)
    (actual : Matrix) (work left : Nat)
    (read : (Raw.ProtectedEvaluation.eventMatrix dependencies operation).run work = (.ok actual,left)) :
    EventAction dependencies operation actual := by
  cases operation
  case computed bits axes source ancilla function uses logical =>
    exact computed_event_action dependencies bits axes source ancilla function uses logical actual work left read
  case protectedComputed bits axes source ancilla function uses =>
    exact protected_event_action dependencies bits axes source ancilla function uses actual work left read
  all_goals exact ordinary_event_action dependencies _ actual work left read True.intro

/-- The actual reconstruction and the independent reader use the same
complete ordered event list on arbitrary complex reference columns. -/
theorem program_action (dependencies : List Dependency) (program : Semantics.Raw.Program)
    (actual : Matrix) (work left : Nat)
    (read : (Raw.ProtectedEvaluation.reconstruct dependencies program).run work = (.ok actual,left))
    (trace : Semantics.RawTrace.Prepared) (original : Semantics.RawTrace.run program = some trace)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < actual.rows) :
    action actual joint row reference =
      Qleisli.Semantics.RawAction.events dependencies trace.events (fun col => joint col reference) row := by
  obtain ⟨checked,ran,equal⟩ := reconstruct_action dependencies program actual work left read
    (event_action dependencies)
  have same := Option.some.inj (ran.symm.trans original)
  subst checked
  exact equal joint row reference bounded

#print axioms program_action
end Qleisli.Raw.ReconstructedAction
