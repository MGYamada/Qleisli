import ProtectedClean
import Qleisli.RawPure
import Qleisli.FiniteMatrixAction
import Qleisli.RuntimeComputedProtectedAction
import Qleisli.RuntimeForestProduct

/-! Exact cleanup in the actual ordered pure Raw program. Certified scopes
retain their original physical circuit and independently requested logical
circuit. Protected scopes use QPTL's uncompute square. Every physical row,
including dirty auxiliary rows, is covered before the local action is composed.
No source-preservation, general CPTP-marginal or quantitative resource claim is
made here, and no acceptance rule or executable bound is changed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Raw.ProtectedProgram
open CategoryTheory
open QleisliKernel
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Function
open QleisliKernel.Raw QleisliKernel.Raw.Pure QleisliKernel.Finite
open Qleisli.Semantics.Exact Qleisli.Semantics.Raw

private theorem zero_map_action {bits physicalBits : Nat} {actual : Matrix}
    (meaning : MapMeaning bits physicalBits (List.range (2^bits)) actual)
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R)
    (bounded : row < actual.rows) :
    action actual joint row reference = if row < 2^bits then joint row reference else 0 := by
  unfold action
  rw [meaning.2.1]
  have columns : ((List.range (2^bits)).map
      (fun col => entry actual row col * joint col reference)).sum =
      ((List.range (2^bits)).map (fun col => if row = col then joint col reference else 0)).sum := by
    apply Qleisli.Exact.sum_map_congr
    intro col member
    have inside := List.mem_range.mp member
    rw [meaning.2.2 row col bounded (meaning.2.1.symm ▸ inside)]
    rw [List.getElem?_range inside]
    simp only [beq_iff_eq, Option.some.injEq]
    by_cases same : row = col
    · subst row
      rw [if_pos rfl, if_pos rfl, one_mul]
    · rw [if_neg (Ne.symm same), if_neg same, zero_mul]
  rw [columns]
  by_cases inside : row < 2^bits
  · rw [if_pos inside]
    exact Qleisli.Exact.range_delta_sum _ _ _ inside
  · rw [if_neg inside]
    apply List.sum_eq_zero
    intro value present
    obtain ⟨col,inRange,rfl⟩ := List.mem_map.mp present
    have different : row ≠ col := fun equal => inside (equal ▸ List.mem_range.mp inRange)
    exact if_neg different

/-- Actual local certificate success gives zero return on every physical row,
not merely agreement after projecting away the auxiliary. The requested
logical matrix is the independently reconstructed logical circuit. -/
theorem certified_clean_action (dependencies : List Dependency)
    (sourceBits dataBits ancillaBits : Nat) (function : List Nat)
    (uses logicalSteps : List Step) (logical : Matrix) (work left : Nat)
    (accepted : (Raw.clean dependencies sourceBits dataBits ancillaBits function uses logicalSteps).run work =
      (.ok logical,left))
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R)
    (bounded : row < 2^(dataBits+ancillaBits)) :
    Qleisli.Semantics.RawAction.circuit dependencies
        ([Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
          [Raw.computeStep sourceBits dataBits ancillaBits function])
        (fun col => if col < 2^dataBits then joint col reference else 0) row =
      if row < 2^dataBits then action logical joint row reference else 0 := by
  obtain ⟨encoding,physical,_,_,c,d,e,f,_,zeroRead,physicalRead⟩ :=
    Raw.clean_conditions _ _ _ _ _ _ _ _ _ _ accepted
  obtain ⟨_,_,start,finish,encoded⟩ := Raw.zeroEncoding_value _ _ _ c d zeroRead
  have meaning := Qleisli.Raw.mapping_denotes _ _ _ _ start finish encoded
  let tape := [Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
    [Raw.computeStep sourceBits dataBits ancillaBits function]
  let circuit := Raw.circuit (dataBits+ancillaBits) tape
  let contract : Contract := ⟨encoding,encoding,logical⟩
  have checked : (check dependencies circuit contract contract).run e = (.ok physical,f) := physicalRead
  obtain ⟨_,cols,_,rows,_,_⟩ := Qleisli.Finite.check_encoded _ _ _ _ _ _ _ checked
  have codeBound : row < encoding.map.rows := meaning.1.symm ▸ bounded
  have physicalBound : row < physical.rows := rows.symm ▸ codeBound
  obtain ⟨_,_,_,_,_,_,circuitWork,circuitLeft,_,_,_,_,circuitRead,_,_,_⟩ :=
    check_conditions _ _ _ _ _ _ _ checked
  let padded := fun col ref => if col < 2^dataBits then joint col ref else 0
  symm
  calc
    _ = action encoding.map (fun col ref => action logical joint col ref) row reference :=
      (zero_map_action meaning _ row reference codeBound).symm
    _ = action physical (fun col ref => action encoding.map joint col ref) row reference :=
      (Qleisli.Finite.check_reference _ _ _ _ _ _ _ checked joint row reference physicalBound).symm
    _ = action physical padded row reference := by
      unfold action
      apply Qleisli.Exact.sum_map_congr
      intro col member
      have colBound : col < encoding.map.rows := cols ▸ List.mem_range.mp member
      change entry physical row col * action encoding.map joint col reference =
        entry physical row col * padded col reference
      rw [zero_map_action meaning joint col reference colBound]
    _ = _ := Qleisli.Finite.circuitMatrix_action dependencies circuit physical circuitWork circuitLeft
      circuitRead padded row reference physicalBound

/-- Every dirty auxiliary row vanishes, for arbitrary correlated input. -/
theorem certified_clean_dirty (dependencies : List Dependency)
    (sourceBits dataBits ancillaBits : Nat) (function : List Nat)
    (uses logicalSteps : List Step) (logical : Matrix) (work left : Nat)
    (accepted : (Raw.clean dependencies sourceBits dataBits ancillaBits function uses logicalSteps).run work =
      (.ok logical,left))
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R)
    (bounded : row < 2^(dataBits+ancillaBits)) (dirty : 2^dataBits ≤ row) :
    Qleisli.Semantics.RawAction.circuit dependencies
        ([Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
          [Raw.computeStep sourceBits dataBits ancillaBits function])
        (fun col => if col < 2^dataBits then joint col reference else 0) row = 0 := by
  rw [certified_clean_action _ _ _ _ _ _ _ _ _ _ accepted joint row reference bounded]
  exact if_neg (Nat.not_lt.mpr dirty)

abbrev FiniteState (bits : Nat) (R : Type) := Fin (2^bits) → R → ℂ

/-- The stated zero image in the complete finite physical interface. -/
noncomputable def zeroImage {R : Type} (dataBits ancillaBits : Nat)
    (joint : Nat → R → ℂ) : FiniteState (dataBits+ancillaBits) R :=
  fun row reference => if row.val < 2^dataBits then joint row.val reference else 0

noncomputable def finiteCircuit {R : Type} (dependencies : List Dependency) (bits : Nat)
    (steps : List Step) (joint : FiniteState bits R) : FiniteState bits R :=
  fun row reference => Qleisli.Semantics.RawAction.circuit dependencies steps
    (fun col => if inside : col < 2^bits then joint ⟨col,inside⟩ reference else 0) row.val

/-- The certificate path supplies the same exact kind of commuting square as
the structured path. The bottom morphism acts on every finite physical row. -/
theorem certified_clean_square {R : Type} (dependencies : List Dependency)
    (sourceBits dataBits ancillaBits : Nat) (function : List Nat)
    (uses logicalSteps : List Step) (logical : Matrix) (work left : Nat)
    (accepted : (Raw.clean dependencies sourceBits dataBits ancillaBits function uses logicalSteps).run work =
      (.ok logical,left)) :
    CommSq (TypeCat.ofHom (action logical (R := R)))
      (TypeCat.ofHom (zeroImage dataBits ancillaBits))
      (TypeCat.ofHom (zeroImage dataBits ancillaBits))
      (TypeCat.ofHom (finiteCircuit dependencies (dataBits+ancillaBits)
        ([Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
          [Raw.computeStep sourceBits dataBits ancillaBits function]))) := by
  refine ⟨?_⟩
  apply ConcreteCategory.hom_ext
  intro joint
  funext row reference
  have padding : (fun col => if inside : col < 2^(dataBits+ancillaBits) then
        zeroImage dataBits ancillaBits joint ⟨col,inside⟩ reference else 0) =
      (fun col => if col < 2^dataBits then joint col reference else 0) := by
    funext col
    by_cases physical : col < 2^(dataBits+ancillaBits)
    · simp only [dif_pos physical, zeroImage]
    · have outside : ¬ col < 2^dataBits := by
        intro inside
        exact physical (Nat.lt_of_lt_of_le inside (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [dif_neg physical, if_neg outside]
  change (if row.val < 2^dataBits then action logical joint row.val reference else 0) =
    Qleisli.Semantics.RawAction.circuit dependencies
      ([Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
        [Raw.computeStep sourceBits dataBits ancillaBits function])
      (fun col => if inside : col < 2^(dataBits+ancillaBits) then
        zeroImage dataBits ancillaBits joint ⟨col,inside⟩ reference else 0) row.val
  rw [padding]
  exact (certified_clean_action _ _ _ _ _ _ _ _ _ _ accepted joint row.val reference row.isLt).symm

/-- The actual protected event check supplies the structured square; the
inverse is the literal XOR involution, not an assumed final clean equation. -/
theorem protected_event_square {R : Type} (dependencies : List Dependency)
    (bits : Nat) (axes : List Nat) (sourceBits ancillaBits : Nat)
    (function : List Nat) (uses : List Use) (work left : Nat)
    (accepted : (eventCheck dependencies
      (.protectedComputed bits axes sourceBits ancillaBits function uses)).run work = (.ok (),left)) :
    let f := fun source => function[source]?.getD 0
    CommSq (TypeCat.ofHom (Qleisli.Semantics.Protected.logical (R := R) f uses))
      (TypeCat.ofHom Qleisli.Semantics.Protected.zero)
      (TypeCat.ofHom Qleisli.Semantics.Protected.zero)
      (TypeCat.ofHom (Qleisli.Semantics.Protected.compute f) ≫
        TypeCat.ofHom (Qleisli.Semantics.Protected.run uses) ≫
        TypeCat.ofHom (Qleisli.Semantics.Protected.compute f)) := by
  intro f
  have valid := (guard_success _ _ _ _ accepted).1
  simp only [Bool.and_eq_true] at valid
  apply QPTL.uncompute_square
    (Qleisli.Raw.ProtectedClean.computed_square f uses (Qleisli.Raw.uses_valid_diagonal _ _ _ _ valid.2))
  apply ConcreteCategory.hom_ext
  intro joint
  change Qleisli.Semantics.Protected.compute f (Qleisli.Semantics.Protected.compute f joint) = joint
  funext source ancilla target reference
  simp only [Qleisli.Semantics.Protected.compute,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]


/-- The clean result of the actual checked scope uses the original predicate
and original auxiliary body. The equation holds at every auxiliary coordinate
and for arbitrary reference-indexed amplitudes. -/
theorem original_protected_clean_action
    {sources caller dependencies program block start count event prepared interval before}
    (checked : @Qirf.RuntimeComputedUse.Checked sources caller dependencies program block start count
      event prepared interval before)
    {R : Type} (ψ : Qleisli.Semantics.Protected.Logical R)
    (source auxiliary target : Nat) (reference : R)
    {choice : Nat} (chosen : prepared.predicate.table[source]? = some choice) (bit : choice = 0 ∨ choice = 1) :
    let f := fun row => checked.literal.table[row]?.getD 0
    Qleisli.Semantics.Protected.compute f
      (Qleisli.Semantics.Protected.run checked.literal.uses
        (Qleisli.Semantics.Protected.compute f (Qleisli.Semantics.Protected.zero ψ)))
      source auxiliary target reference =
      if auxiliary = 0 then ψ source target reference * scalar (prepared.action.matrix.entry choice choice) else 0 := by
  intro f
  obtain ⟨result,dispatched⟩ := checked.literal.dispatch
  obtain ⟨_,_,_,_,_,clean⟩ := Qleisli.Raw.ProtectedClean.accepted_clean_action
    (dependencies.map (·.signature)) interval.before.quantum checked.literal.input.port.token
    checked.literal.output.token [] [checked.literal.auxiliary] checked.literal.table checked.literal.uses
    result dispatched ψ
  rw [clean]
  simp only [Qleisli.Semantics.Protected.zero,
    Qleisli.RuntimeComputedProtectedAction.original_phase checked ψ source target reference chosen bit]

#print axioms original_protected_clean_action

/-- The independently requested local action, embedded on the original axes.
Only clean scopes are replaced; all other events retain their literal action. -/
noncomputable def logicalEvent (dependencies : List Dependency) (operation : Event)
    (joint : Nat → ℂ) : Nat → ℂ :=
  match operation with
  | .computed _ axes _ _ _ _ logicalSteps =>
    Qleisli.Semantics.RawAction.embed axes
      (Qleisli.Semantics.RawAction.circuit dependencies logicalSteps) joint
  | .protectedComputed _ axes sourceBits _ function uses =>
    Qleisli.Semantics.RawAction.embed axes (fun input output =>
      Qleisli.Semantics.Protected.logical (fun source => function[source]?.getD 0) uses
        (fun source target (_ : Unit) => input (source+target*2^sourceBits))
        (output % 2^sourceBits) (output / 2^sourceBits) ()) joint
  | event => Qleisli.Semantics.RawAction.event dependencies event joint

noncomputable def logicalEvents (dependencies : List Dependency) (operations : List Event)
    (joint : Nat → ℂ) : Nat → ℂ := operations.foldl (fun joint event => logicalEvent dependencies event joint) joint

/-- Each successful original event check permits this exact local replacement.
The certified case first proves all-row cleanliness; the protected case uses
the QPTL square above. No new logical circuit is guessed from its name. -/
theorem event_action (dependencies : List Dependency) (operation : Event) (work left : Nat)
    (accepted : (eventCheck dependencies operation).run work = (.ok (),left)) (joint : Nat → ℂ) :
    Qleisli.Semantics.RawAction.event dependencies operation joint = logicalEvent dependencies operation joint := by
  cases operation with
  | circuit _ _ | init0 _ | liftBasis _ _ _ _ _ | reorder _ _ => rfl
  | computed bits axes sourceBits ancillaBits function uses logicalSteps =>
    obtain ⟨logical,middle,clean,_⟩ := bind_success _ _ _ _ _ accepted
    obtain ⟨_,_,a,b,_,_,_,_,logicalRead,_,_⟩ :=
      Raw.clean_conditions _ _ _ _ _ _ _ _ _ _ clean
    have logicalRows : logical.rows = 2^axes.length := by
      obtain ⟨columns,_,equal⟩ := Qleisli.Raw.circuit_denotes _ _ _ _ a b logicalRead
      exact congrArg Matrix.rows equal
    funext row
    let input : Nat → Unit → ℂ := fun col _ => joint (scatter row axes col)
    have localBound := Qleisli.RuntimeForestProduct.gather_bound row axes
    have physicalBound : gather row axes < 2^(axes.length+ancillaBits) :=
      Nat.lt_of_lt_of_le localBound (Nat.pow_le_pow_right (by decide) (by omega))
    change Qleisli.Semantics.RawAction.circuit dependencies
      ([Raw.computeStep sourceBits axes.length ancillaBits function] ++ uses ++
        [Raw.computeStep sourceBits axes.length ancillaBits function])
      (fun col => if col < 2^axes.length then input col () else 0) (gather row axes) =
      Qleisli.Semantics.RawAction.circuit dependencies logicalSteps (fun col => input col ()) (gather row axes)
    rw [certified_clean_action _ _ _ _ _ _ _ _ _ _ clean input _ () physicalBound,if_pos localBound]
    exact Qleisli.Finite.circuitMatrix_action dependencies (Raw.circuit axes.length logicalSteps)
      logical a b logicalRead input _ () (logicalRows.symm ▸ localBound)
  | protectedComputed bits axes sourceBits ancillaBits function uses =>
    have square := protected_event_square (R := Unit) dependencies bits axes sourceBits ancillaBits
      function uses work left accepted
    funext row
    let input : Qleisli.Semantics.Protected.Logical Unit := fun source target _ =>
      joint (scatter row axes (source+target*2^sourceBits))
    have factor := (ConcreteCategory.congr_hom square.w input).symm
    have coordinate := congrArg (fun state =>
      state (gather row axes % 2^sourceBits) 0 (gather row axes / 2^sourceBits) ()) factor
    simpa only [Qleisli.Semantics.RawAction.event,Qleisli.Semantics.RawAction.embed,
      logicalEvent,Qleisli.Semantics.Protected.zero,if_pos rfl] using coordinate

/-- Replacement commutes with the complete original event order. -/
theorem events_action (dependencies : List Dependency) (operations : List Event)
    (accepted : ∀ event ∈ operations, ∃ work left, (eventCheck dependencies event).run work = (.ok (),left))
    (joint : Nat → ℂ) :
    Qleisli.Semantics.RawAction.events dependencies operations joint = logicalEvents dependencies operations joint := by
  induction operations generalizing joint with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨work,left,checked⟩ := accepted event List.mem_cons_self
    change Qleisli.Semantics.RawAction.events dependencies rest
      (Qleisli.Semantics.RawAction.event dependencies event joint) =
      logicalEvents dependencies rest (logicalEvent dependencies event joint)
    rw [event_action dependencies event work left checked joint]
    exact ih (fun event member => accepted event (List.mem_cons_of_mem _ member)) _

/-- Actual verification, rather than an externally supplied event list, binds
the complete ordered replacement to the original program. References may be
arbitrarily correlated and carry arbitrary complex amplitudes. -/
theorem verify_action {R : Type} (dependencies : List Dependency) (body : Program)
    (prepared : Prepared) (work left : Nat)
    (accepted : (verify dependencies body).run work = (.ok prepared,left))
    (joint : Nat → R → ℂ) (reference : R) :
    Qleisli.Semantics.RawAction.program dependencies body (fun row => joint row reference) =
      some (logicalEvents dependencies prepared.events (fun row => joint row reference)) := by
  have original := Qleisli.Raw.Pure.verify_complex_denotation _ _ _ _ _ accepted (fun row => joint row reference)
  exact original.trans (congrArg some (events_action dependencies prepared.events
    (verify_conditions _ _ _ _ _ accepted).2.2 _))

/-- Fresh graph inspection binds the original program, all dependency bodies,
and its complete clean-scope replacement. This is a Raw Soundness statement,
not a source compiler, observation-channel or target-resource theorem. -/
theorem inspect_action {R : Type} (inputs : List Input) (bindings : List Binding) (body : Program)
    (checked : Checked) (work left : Nat)
    (accepted : (inspect inputs bindings body).run work = (.ok checked,left)) :
    checked.program = body ∧ Function.GraphMeaning checked.receipts ∧
      checked.receipts.map (·.input) = inputs ∧ inputs = bindings ∧
      ∀ (joint : Nat → R → ℂ) reference,
        Qleisli.Semantics.RawAction.program (checked.receipts.map Receipt.dependency) body
          (fun row => joint row reference) =
        some (logicalEvents (checked.receipts.map Receipt.dependency) checked.prepared.events
          (fun row => joint row reference)) := by
  obtain ⟨bodyEq,a,b,c,d,graphRead,programRead⟩ := inspect_fresh _ _ _ _ _ _ accepted
  obtain ⟨graph,identities,binding⟩ := Qleisli.Raw.Function.checkAll_semantics _ _ _ _ _ graphRead
  exact ⟨bodyEq,graph,identities,binding,fun joint reference =>
    verify_action _ _ _ _ _ programRead joint reference⟩

#print axioms certified_clean_action
#print axioms certified_clean_dirty
#print axioms certified_clean_square
#print axioms protected_event_square
#print axioms event_action
#print axioms events_action
#print axioms verify_action
#print axioms inspect_action
end Qleisli.Raw.ProtectedProgram
