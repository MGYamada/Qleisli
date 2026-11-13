import Qleisli.RawProtectedEvaluation
import Qleisli.FiniteMatrixAction
import Qleisli.RuntimeFiniteTargetScatter
import QleisliKernel.Raw.Trace

/-! Compare the actual reconstructed physical matrices with the independent
literal Raw action on arbitrary complex reference columns.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.ReconstructedAction
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Event Program Use)
open Qleisli.Semantics.Exact Qleisli.Semantics.Raw
open Qleisli.Semantics.RawAction (event events)

/-- Agreement with one literal event on the finite output of its matrix. -/
def EventAction (dependencies : List Dependency) (operation : Event) (actual : Matrix) : Prop :=
  ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row reference, row < actual.rows →
    action actual joint row reference = event dependencies operation (fun col => joint col reference) row

private theorem mapping_action {inputBits outputBits : Nat} {labels : List Nat} {actual : Matrix}
    (meaning : MapMeaning inputBits outputBits labels actual)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < actual.rows) :
    action actual joint row reference = ((List.range (2^inputBits)).map fun col =>
      if labels[col]? = some row then joint col reference else 0).sum := by
  unfold action
  rw [meaning.2.1]
  apply Qleisli.Exact.sum_map_congr
  intro col member
  have colBound : col < actual.cols := meaning.2.1.symm ▸ List.mem_range.mp member
  rw [meaning.2.2 row col bounded colBound]
  by_cases selected : labels[col]? = some row <;> simp [selected]

private theorem mapped_action {inputBits outputBits : Nat} {actual : Matrix}
    (label : Nat → Nat)
    (meaning : MapMeaning inputBits outputBits ((List.range (2^inputBits)).map label) actual)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < actual.rows) :
    action actual joint row reference = ((List.range (2^inputBits)).map fun col =>
      if label col == row then joint col reference else 0).sum := by
  rw [mapping_action meaning joint row reference bounded]
  apply Qleisli.Exact.sum_map_congr
  intro col member
  have inside := List.mem_range.mp member
  simp [inside]

private theorem allocation_action {bits outputBits : Nat} {actual : Matrix}
    (meaning : MapMeaning bits outputBits (List.range (2^bits)) actual)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < actual.rows) :
    action actual joint row reference = if row < 2^bits then joint row reference else 0 := by
  rw [mapping_action meaning joint row reference bounded]
  calc
    _ = ((List.range (2^bits)).map fun col => if row = col then joint col reference else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro col member
      have colBound := List.mem_range.mp member
      simp [colBound,eq_comm]
    _ = _ := by
      by_cases inside : row < 2^bits
      · rw [if_pos inside]
        exact Qleisli.Exact.range_delta_sum _ _ _ inside
      · rw [if_neg inside]
        have zero : (List.range (2^bits)).map (fun col => if row = col then joint col reference else 0) =
            (List.range (2^bits)).map (fun _ => (0 : ℂ)) := by
          apply List.map_congr_left
          intro col member
          have different : row ≠ col := fun same => inside (same ▸ List.mem_range.mp member)
          simp [different]
        simp [zero]

/-- The same event read gives the literal action for circuits, allocation,
basis maps and reorder. Computed events have separate encoded-image laws. -/
theorem ordinary_event_action (dependencies : List Dependency) (operation : Event)
    (actual : Matrix) (work left : Nat)
    (read : (Raw.ProtectedEvaluation.eventMatrix dependencies operation).run work = (.ok actual,left))
    (ordinary : match operation with
      | .computed .. | .protectedComputed .. => False
      | _ => True) :
    EventAction dependencies operation actual := by
  intro Reference joint row reference bound
  cases operation with
  | circuit bits steps =>
    obtain ⟨_,middle,_,circuit⟩ := bind_success _ _ _ _ _ read
    exact Qleisli.Finite.circuitMatrix_action dependencies (Raw.circuit bits steps) actual middle left
      circuit joint row reference bound
  | init0 bits =>
    obtain ⟨_,middle,_,mapping⟩ := bind_success _ _ _ _ _ read
    exact allocation_action (Qleisli.Raw.mapping_denotes _ _ _ _ middle left mapping)
      joint row reference bound
  | liftBasis before after inputAxes outputAxes table =>
    obtain ⟨_,middle,_,mapping⟩ := bind_success _ _ _ _ _ read
    exact mapped_action _ (Qleisli.Raw.mapping_denotes _ _ _ _ middle left mapping)
      joint row reference bound
  | reorder bits axes =>
    obtain ⟨_,middle,_,mapping⟩ := bind_success _ _ _ _ _ read
    exact mapped_action _ (Qleisli.Raw.mapping_denotes _ _ _ _ middle left mapping)
      joint row reference bound
  | computed _ _ _ _ _ _ _ | protectedComputed _ _ _ _ _ _ => exact False.elim ordinary

private theorem scatter_fibre (axes : List Nat) (unique : axes.Nodup) (row col : Nat) :
    scatter col axes (gather row axes) = row ↔ scatter row axes (gather col axes) = col := by
  have flip (a b : Nat) (same : scatter a axes (gather b axes) = b) :
      scatter b axes (gather a axes) = a := by
    calc
      _ = scatter (scatter a axes (gather b axes)) axes (gather a axes) :=
        congrArg (fun base => scatter base axes (gather a axes)) same.symm
      _ = scatter a axes (gather a axes) :=
        Qleisli.RuntimeFiniteTargetScatter.scatter_overwrite _ _ _ _ unique
      _ = _ := QleisliKernel.Qirf.RuntimeScatterTransport.scatter_gather _ _ unique
  exact ⟨flip col row,flip row col⟩

/-- The native promoted matrix applies its local map to the exact selected
coordinates of each physical row. The original unselected bits and the
arbitrary reference coefficient are retained together. -/
theorem promoted_action {bits : Nat} {axes : List Nat} {logical actual : Matrix}
    (work left : Nat) (read : (Raw.promote bits axes logical).run work = (.ok actual,left))
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < actual.rows) :
    action actual joint row reference =
      action logical (fun col ref => joint (scatter row axes col) ref) (gather row axes) reference := by
  have embedded := Qleisli.Raw.promote_denotes _ _ _ _ work left read
  obtain ⟨_,_,guarded,_⟩ := bind_success _ _ _ _ _ read
  have checked := (guard_success _ _ _ _ guarded).1
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at checked
  have geometry := checked.1.1.2
  have localCols := checked.2.trans checked.1.2
  simp only [QleisliKernel.Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at geometry
  have axesBound := geometry.1.2
  have unique := Raw.Ownership.unique_nodup axes geometry.2
  have inside : row < 2^bits := embedded.1 ▸ bounded
  let mask := fun col => scatter col axes (gather row axes) = row
  let weight := fun col => entry logical (gather row axes) (gather col axes) * joint col reference
  have digit (col k : Nat) (bound : k < 2^axes.length) :
      scatter row axes k = col ↔ mask col ∧ gather col axes = k := by
    constructor
    · intro selected
      have coordinate : gather col axes = k :=
        (congrArg (fun label => gather label axes) selected).symm.trans
          (Qleisli.RuntimeFiniteTargetScatter.gather_scatter row k axes unique bound)
      exact ⟨(scatter_fibre axes unique row col).mpr (by rw [coordinate,selected]),coordinate⟩
    · rintro ⟨held,coordinate⟩
      exact coordinate ▸ (scatter_fibre axes unique row col).mp held
  calc
    _ = ((List.range (2^bits)).map (fun col => if mask col then weight col else 0)).sum := by
      unfold action
      rw [embedded.2.1]
      apply Qleisli.Exact.sum_map_congr
      intro col member
      have colBound : col < actual.cols := embedded.2.1.symm ▸ List.mem_range.mp member
      rw [embedded.2.2 row col bounded colBound]
      by_cases held : mask col <;> simp [mask,weight,held]
    _ = ((List.range (2^bits)).map (fun col => ((List.range (2^axes.length)).map fun k =>
        if scatter row axes k = col then weight col else 0).sum)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro col _
      have select := Qleisli.Exact.sum_map_congr (List.range (2^axes.length))
        (fun k => if scatter row axes k = col then weight col else 0)
        (fun k => if mask col ∧ gather col axes = k then weight col else 0)
        (fun k member => by
          dsimp only
          by_cases selected : scatter row axes k = col
          · have held := (digit col k (List.mem_range.mp member)).mp selected
            simp [selected,held]
          · have absent := fun held => selected ((digit col k (List.mem_range.mp member)).mpr held)
            exact (if_neg selected).trans (if_neg absent).symm)
      rw [select]
      by_cases held : mask col
      · simp only [held,true_and,if_true]
        exact (Qleisli.Exact.range_delta_sum _ _ (fun _ => weight col)
          (Qleisli.RuntimeForestProduct.gather_bound col axes)).symm
      · simp [held]
    _ = ((List.range (2^axes.length)).map (fun k => ((List.range (2^bits)).map fun col =>
        if scatter row axes k = col then weight col else 0).sum)).sum :=
      Qleisli.Exact.sum_swap _ _ _
    _ = _ := by
      unfold action
      rw [localCols]
      apply Qleisli.Exact.sum_map_congr
      intro k member
      calc
        _ = weight (scatter row axes k) := Qleisli.Exact.range_delta_sum (2^bits) (scatter row axes k) weight
          (Qleisli.Finite.Pull.scatter_bound row bits k axes inside axesBound)
        _ = _ := by
          dsimp only [weight]
          rw [Qleisli.RuntimeFiniteTargetScatter.gather_scatter row k axes unique (List.mem_range.mp member)]

theorem clean_action {dependencies : List Dependency} {sourceBits dataBits ancillaBits : Nat}
    {function : List Nat} {uses logicalSteps : List Step} {logical : Matrix} (work left : Nat)
    (read : (Raw.clean dependencies sourceBits dataBits ancillaBits function uses logicalSteps).run work =
      (.ok logical,left))
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < 2^dataBits) :
    action logical joint row reference =
      Qleisli.Semantics.RawAction.circuit dependencies
        ([Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
          [Raw.computeStep sourceBits dataBits ancillaBits function])
        (fun col => if col < 2^dataBits then joint col reference else 0) row := by
  obtain ⟨encoding,physical,_,_,c,d,e,f,_,zeroRead,physicalRead⟩ :=
    Raw.clean_conditions _ _ _ _ _ _ _ _ _ _ read
  obtain ⟨_,_,start,finish,encoded⟩ := Raw.zeroEncoding_value _ _ _ c d zeroRead
  have meaning := Qleisli.Raw.mapping_denotes _ _ _ _ start finish encoded
  let tape := [Raw.computeStep sourceBits dataBits ancillaBits function] ++ uses ++
    [Raw.computeStep sourceBits dataBits ancillaBits function]
  let circuit := Raw.circuit (dataBits+ancillaBits) tape
  let contract : Contract := ⟨encoding,encoding,logical⟩
  have checked : (check dependencies circuit contract contract).run e = (.ok physical,f) := physicalRead
  obtain ⟨_,cols,_,rows,_,_⟩ := Qleisli.Finite.check_encoded _ _ _ _ _ _ _ checked
  have codeBound : row < encoding.map.rows :=
    meaning.1.symm ▸ Nat.lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide) (by omega))
  have physicalBound : row < physical.rows := rows.symm ▸ codeBound
  obtain ⟨_,_,_,_,_,_,circuitWork,circuitLeft,_,_,_,_,circuitRead,_,_,_⟩ :=
    check_conditions _ _ _ _ _ _ _ checked
  let padded := fun col ref => if col < 2^dataBits then joint col ref else 0
  calc
    _ = action encoding.map (fun col ref => action logical joint col ref) row reference := by
      rw [allocation_action meaning _ row reference codeBound,if_pos bounded]
    _ = action physical (fun col ref => action encoding.map joint col ref) row reference :=
      (Qleisli.Finite.check_reference _ _ _ _ _ _ _ checked joint row reference physicalBound).symm
    _ = action physical padded row reference := by
      unfold action
      apply Qleisli.Exact.sum_map_congr
      intro col member
      have colBound : col < encoding.map.rows := cols ▸ List.mem_range.mp member
      change entry physical row col * action encoding.map joint col reference =
        entry physical row col * padded col reference
      rw [allocation_action meaning joint col reference colBound]
    _ = _ := Qleisli.Finite.circuitMatrix_action dependencies circuit physical circuitWork circuitLeft
      circuitRead padded row reference physicalBound

/-- The computed event uses the checked zero-image equation of the actual
compute/use/inverse circuit and the same selected coordinates as its matrix. -/
theorem computed_event_action (dependencies : List Dependency) (bits : Nat) (axes : List Nat)
    (sourceBits ancillaBits : Nat) (function : List Nat) (uses logicalSteps : List Step)
    (actual : Matrix) (work left : Nat)
    (read : (Raw.ProtectedEvaluation.eventMatrix dependencies
      (.computed bits axes sourceBits ancillaBits function uses logicalSteps)).run work = (.ok actual,left)) :
    EventAction dependencies (.computed bits axes sourceBits ancillaBits function uses logicalSteps) actual := by
  intro Reference joint row reference bound
  obtain ⟨_,middle,_,remaining⟩ := bind_success _ _ _ _ _ read
  obtain ⟨logical,after,clean,promote⟩ := bind_success _ _ _ _ _ remaining
  rw [promoted_action after left promote joint row reference bound]
  exact clean_action middle after clean (fun col ref => joint (scatter row axes col) ref)
    (gather row axes) reference (Qleisli.RuntimeForestProduct.gather_bound row axes)

/-- A coefficient of the checked protected matrix uses the original physical
compute/use/inverse action on precisely the written input basis column. -/
theorem protected_matrix_entry {sourceBits dataBits ancillaBits : Nat}
    {function : List Nat} {uses : List Use} {actual : Matrix} (work left : Nat)
    (read : (Raw.ProtectedEvaluation.matrix sourceBits dataBits ancillaBits function uses).run work =
      (.ok actual,left))
    (row col : Nat) (rowBound : row < 2^dataBits) (colBound : col < 2^dataBits) :
    entry actual row col =
      Qleisli.Semantics.ProtectedMatrix.coefficient sourceBits function uses (2^dataBits)
        (row*(2^dataBits)+col) := by
  obtain ⟨_,columns,values⟩ := Qleisli.Raw.ProtectedEvaluation.matrix_meaning _ _ _ _ _ _ _ _ read
  have indexBound : row*(2^dataBits)+col < (2^dataBits)*(2^dataBits) := by nlinarith
  have rangeBound : row*(2^dataBits)+col < (List.range ((2^dataBits)*(2^dataBits))).length := by
    simpa only [List.length_range] using indexBound
  have entriesBound : row*(2^dataBits)+col < actual.entries.length :=
    values.length_eq ▸ rangeBound
  have exactEntry := values.get (i := row*(2^dataBits)+col) rangeBound entriesBound
  simpa only [entry,Matrix.entry,columns,List.get_eq_getElem,List.getElem_range,
    List.getElem?_eq_getElem entriesBound,Option.getD_some] using exactEntry

private theorem identity_action {bits : Nat} {initial : Matrix}
    (read : QleisliKernel.Exact.Matrix.identity (2^bits) = .ok initial)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < initial.rows) :
    action initial joint row reference = joint row reference := by
  obtain ⟨_,rows,cols,entries⟩ := Qleisli.Exact.identity_meaning _ _ read
  have inside : row < 2^bits := rows ▸ bounded
  unfold action
  rw [cols]
  calc
    _ = ((List.range (2^bits)).map (fun col => if row = col then joint col reference else 0)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro col member
      rw [entries row col inside (List.mem_range.mp member)]
      split <;> simp
    _ = _ := Qleisli.Exact.range_delta_sum _ _ _ inside

/-- The exact successful event compositions act as the original ordered
event list whenever the individual event reads have their literal actions. -/
theorem events_action (dependencies : List Dependency) (operations : List Event)
    (initial actual : Matrix) (work left : Nat)
    (read : (operations.foldlM (Raw.ProtectedEvaluation.evolve dependencies) initial).run work =
      (.ok actual,left))
    (localActions : ∀ operation ∈ operations, ∀ matrix w r,
      (Raw.ProtectedEvaluation.eventMatrix dependencies operation).run w = (.ok matrix,r) →
        EventAction dependencies operation matrix)
    {Reference : Type} (joint initialValues : Nat → Reference → ℂ)
    (started : ∀ row reference, row < initial.rows → action initial joint row reference = initialValues row reference)
    (row : Nat) (reference : Reference) (bounded : row < actual.rows) :
    action actual joint row reference =
      events dependencies operations (fun col => initialValues col reference) row := by
  induction operations generalizing initial work initialValues with
  | nil =>
    have same := (pure_success _ _ _ _ read).1
    subst actual
    exact started row reference bounded
  | cons operation rest ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨next,middle,first,tail⟩ := bind_success _ _ _ _ _ read
    obtain ⟨matrix,after,eventRead,composed⟩ := bind_success _ _ _ _ _ first
    have compose := exactWork_success _ _ _ _ composed
    obtain ⟨shape,rows,_,_⟩ := Qleisli.Exact.compose_meaning _ _ _ _ _ compose
    let values := fun col ref => event dependencies operation (fun index => initialValues index ref) col
    apply ih next middle tail (fun op member => localActions op (List.mem_cons_of_mem _ member)) values
    intro output ref inside
    have outputBound : output < matrix.rows := rows ▸ inside
    have localAct := localActions operation List.mem_cons_self matrix work after eventRead
      initialValues output ref outputBound
    rw [Qleisli.Exact.compose_action _ _ _ _ _ compose joint output ref outputBound]
    calc
      _ = action matrix initialValues output ref := by
        unfold action
        apply Qleisli.Exact.sum_map_congr
        intro col member
        change entry matrix output col * action initial joint col ref =
          entry matrix output col * initialValues col ref
        rw [started col ref (shape ▸ List.mem_range.mp member)]
      _ = _ := localAct

/-- The actual reconstruction uses the identity and the exact same trace as
the independent reader. The per-event obligation is discharged on its reads. -/
theorem reconstruct_action (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (read : (Raw.ProtectedEvaluation.reconstruct dependencies program).run work = (.ok actual,left))
    (localActions : ∀ operation matrix w r,
      (Raw.ProtectedEvaluation.eventMatrix dependencies operation).run w = (.ok matrix,r) →
        EventAction dependencies operation matrix) :
    ∃ trace, Semantics.RawTrace.run program = some trace ∧
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row reference, row < actual.rows →
        action actual joint row reference = events dependencies trace.events (fun col => joint col reference) row := by
  unfold Raw.ProtectedEvaluation.reconstruct at read
  obtain ⟨_,a,_,h⟩ := bind_success _ _ _ _ _ read
  obtain ⟨prepared,b,opened,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,d,initialRead,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,e,evolved,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,f,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,g,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have traced := Raw.prepare_reference _ _ _ (lift_success _ _ _ _ opened).1
  have identity := arithmetic_success _ _ (lift_success _ _ _ _ initialRead).1
  refine ⟨prepared.reference,traced,?_⟩
  intro Reference joint row reference bounded
  exact events_action dependencies prepared.events initial result d e evolved
    (fun operation _ => localActions operation) joint joint (identity_action identity joint) row reference bounded

#print axioms ordinary_event_action
#print axioms promoted_action
#print axioms computed_event_action
#print axioms protected_matrix_entry
#print axioms events_action
#print axioms reconstruct_action
end Qleisli.Raw.ReconstructedAction
