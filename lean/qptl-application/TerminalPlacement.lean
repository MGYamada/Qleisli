import Qleisli.RuntimeForestProduct
import Qleisli.RuntimeFiniteTargetScatter
import Qleisli.RawFiniteRows
import Qleisli.RawActionLinear
import Qleisli.FiniteMatrixAction
import Qleisli.RawDenotation
import WorkspaceTargetAction
import RuntimeWorkspaceRestoration
import QleisliKernel.Target.CanonicalOpenQasmPlacement

/-! Relate replayed terminal placement steps to the full physical register,
with exact phase and an arbitrary reference column.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.TerminalPlacement
open scoped BigOperators
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Event)
open Qleisli.RuntimeForestProduct (gather_append gather_bound)
open QleisliKernel.Target.Routing (Swap)
open QleisliKernel.Target.CanonicalOpenQasmPlacement (ReplayOccurrence)
open QleisliKernel.Semantics.RawTrace (Interface)

private def OutsideZero (layout : List Nat) (row : Nat) : Prop :=
  ∀ axis ∉ layout, bit row axis = 0

/-- The entire physical column for an ordered live frame, with the unused
physical lines in their reset state. The inputs need no product assumption. -/
noncomputable def physicalColumn (layout : List Nat) (amplitude : Nat → ℂ) : Nat → ℂ := by
  classical
  exact fun row => if OutsideZero layout row then amplitude (gather row layout) else 0

private theorem outside_append {layout : List Nat} {wire row : Nat}
    (zero : bit row wire = 0) :
    OutsideZero (layout ++ [wire]) row ↔ OutsideZero layout row := by
  constructor
  · intro all axis outside
    by_cases same : axis = wire
    · subst axis
      exact zero
    · exact all axis (by simp [outside, same])
  · intro all axis outside
    exact all axis (fun member => outside (List.mem_append_left _ member))

/-- Issuing a fresh logical owner uses a line already reset by the actual
terminal register initialization. The Raw action adds its high zero bit and
extends the ordered placement. The complete physical amplitudes agree. -/
theorem placed_init_zero (layout : List Nat) (wire : Nat) (fresh : wire ∉ layout)
    (amplitude : Nat → ℂ) :
    physicalColumn (layout ++ [wire])
      (Semantics.RawAction.event [] (.init0 layout.length) amplitude) =
    physicalColumn layout amplitude := by
  classical
  funext row
  have coordinate : gather row (layout ++ [wire]) =
      gather row layout + 2^layout.length * bit row wire := by
    rw [gather_append]
    simp [gather]
  by_cases zero : bit row wire = 0
  · simp [physicalColumn, Semantics.RawAction.event, outside_append zero, coordinate, zero, gather_bound]
  · have absent : ¬OutsideZero layout row := fun all => zero (all wire fresh)
    have above : 2^layout.length ≤ gather row (layout ++ [wire]) := by
      rw [coordinate]
      have enough : 2^layout.length ≤ 2^layout.length * bit row wire :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero zero)
      omega
    simp [physicalColumn, Semantics.RawAction.event, absent, Nat.not_lt.mpr above]

private theorem mem_routed (move : Swap) (layout : List Nat) (axis : Nat) :
    axis ∈ layout.map move.axis ↔ move.axis axis ∈ layout := by
  constructor
  · intro found
    obtain ⟨original,member,equal⟩ := List.mem_map.mp found
    rw [← equal,move.axis_involutive]
    exact member
  · intro found
    exact List.mem_map.mpr ⟨move.axis axis,found,move.axis_involutive axis⟩

private theorem outside_routed (move : Swap) (layout : List Nat) (row : Nat) :
    OutsideZero (layout.map move.axis) row ↔ OutsideZero layout (move.label row) := by
  constructor
  · intro all axis missing
    rw [move.label_bit]
    apply all
    rw [mem_routed,move.axis_involutive]
    exact missing
  · intro all axis missing
    rw [mem_routed] at missing
    have zero := all (move.axis axis) missing
    rwa [move.label_bit,move.axis_involutive] at zero

private theorem swap_action (move : Swap) (distinct : move.first ≠ move.second)
    (amplitude : Nat → ℂ) (row : Nat) :
    Semantics.RawAction.step [] move.step amplitude row = amplitude (move.label row) := by
  have read := move.gather_two row
  have swapped : gather row [move.second,move.first] = bit row move.second + 2 * bit row move.first :=
    (Swap.mk move.second move.first).gather_two row
  have first := QleisliKernel.FiniteRestriction.BitUpdate.bit_lt row move.first
  have second := QleisliKernel.FiniteRestriction.BitUpdate.bit_lt row move.second
  have firstCases : bit row move.first = 0 ∨ bit row move.first = 1 := by omega
  have secondCases : bit row move.second = 0 ∨ bit row move.second = 1 := by omega
  rw [← move.scatter_label row distinct]
  rcases firstCases with low | low <;> rcases secondCases with high | high <;>
    simp [Semantics.RawAction.step, Swap.step, enabled, read, swapped, low, high,
      show List.range 4 = [0,1,2,3] from rfl, Qleisli.Semantics.Finite.phase]

/-- The literal decoded SWAP carries the complete reset-frame embedding to
the routed frame. The same scalar at each live coordinate is preserved. -/
theorem placed_literal_swap (move : Swap) (distinct : move.first ≠ move.second)
    (layout : List Nat) (amplitude : Nat → ℂ) :
    Semantics.RawAction.step []
      (QleisliKernel.Target.CanonicalOpenQasmResources.Instruction.step
        ⟨.swap,[move.first,move.second]⟩) (physicalColumn layout amplitude) =
    physicalColumn (layout.map move.axis) amplitude := by
  classical
  funext row
  change Semantics.RawAction.step [] move.step (physicalColumn layout amplitude) row = _
  rw [swap_action move distinct]
  have gathered := move.gather_placed layout (move.label row)
  rw [move.label_involutive] at gathered
  simp only [physicalColumn,outside_routed,gathered]

#print axioms placed_init_zero
#print axioms placed_literal_swap
private theorem prep_zero_scatter {bits input : Nat} (below : input < 2^bits) :
    scatter input [bits] ([0][gather input []]?.getD 0) = input := by
  have zero : bit input bits = 0 := by
    simp [bit,Nat.div_eq_of_lt below]
  simp [scatter,gather,zero,show bit 0 0 = 0 by rfl]

private theorem list_sum_range (width : Nat) (summand : Nat → ℂ) :
    ((List.range width).map summand).sum = ∑ input ∈ Finset.range width, summand input := by
  induction width with
  | zero => simp
  | succ width ih => simp [List.range_succ,Finset.sum_range_succ,ih]

/-- The exact Raw table event for high zero preparation has the same
coefficient action as native zero allocation for every logical amplitude. -/
theorem prep_zero_action (dependencies : List Dependency) (bits : Nat) (amplitude : Nat → ℂ) :
    Semantics.RawAction.event dependencies (.liftBasis bits (bits+1) [] [bits] [0]) amplitude =
      Semantics.RawAction.event dependencies (.init0 bits) amplitude := by
  funext output
  simp only [Semantics.RawAction.event,list_sum_range]
  calc
    _ = ∑ input ∈ Finset.range (2^bits), (if input = output then amplitude input else 0) := by
      apply Finset.sum_congr rfl
      intro input member
      rw [prep_zero_scatter (Finset.mem_range.mp member)]
      simp
    _ = _ := by simp [Finset.sum_ite_eq']

/-- The source-level zero preparation uses the same unchanged physical
column as a literal Raw zero allocation on the next fresh location. -/
theorem placed_prep_zero (layout : List Nat) (wire : Nat) (fresh : wire ∉ layout)
    (amplitude : Nat → ℂ) :
    physicalColumn (layout ++ [wire])
      (Semantics.RawAction.event [] (.liftBasis layout.length (layout.length+1) [] [layout.length] [0]) amplitude) =
    physicalColumn layout amplitude := by
  rw [prep_zero_action]
  exact placed_init_zero layout wire fresh amplitude

#print axioms prep_zero_action
#print axioms placed_prep_zero

/-- On the actual routing occurrence, the selected physical instruction
advances the reset-frame embedding to precisely the checked next layout. -/
theorem route_preserves_frame {rootDependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior .route suffix)
    (amplitude : Nat → ℂ) :
    ∃ gate, circuit.gates[occurrence.entry.gateIndex]? = some gate ∧
      Semantics.RawAction.step [] gate.step (physicalColumn occurrence.entry.locations amplitude) =
        physicalColumn occurrence.exit.locations amplitude := by
  obtain ⟨first,second,distinct,gate,_,next⟩ := occurrence.route
  refine ⟨_,gate,?_⟩
  rw [next]
  exact placed_literal_swap ⟨first,second⟩ distinct occurrence.entry.locations amplitude

/-- The actual Raw zero preparation is represented by a fresh reset line on
a successful placement occurrence, with no decoded gate consumed. -/
theorem zero_preserves_frame {rootDependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior .original suffix)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {event : Event}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : QleisliKernel.Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[event]))
    (zero : event = .init0 occurrence.entry.locations.length ∨ event = .liftBasis
      occurrence.entry.locations.length (occurrence.entry.locations.length+1) [] [occurrence.entry.locations.length] [0])
    (amplitude : Nat → ℂ) :
    occurrence.exit.gateIndex = occurrence.entry.gateIndex ∧
      physicalColumn occurrence.exit.locations (Semantics.RawAction.event rootDependencies event amplitude) =
        physicalColumn occurrence.entry.locations amplitude := by
  obtain ⟨wire,_,fresh,_,exit,_,_⟩ := occurrence.zero_allocation occurs raw zero
  rw [exit]
  refine ⟨rfl,?_⟩
  rcases zero with rfl | rfl
  · exact placed_init_zero occurrence.entry.locations wire fresh amplitude
  · exact placed_prep_zero occurrence.entry.locations wire fresh amplitude

#print axioms route_preserves_frame
#print axioms zero_preserves_frame

private theorem outside_scatter (row value : Nat) (layout : List Nat) :
    OutsideZero layout (scatter row layout value) ↔ OutsideZero layout row := by
  simp only [OutsideZero]
  exact forall_congr' fun axis => imp_congr_right fun absent =>
    by rw [QleisliKernel.Qirf.RuntimeScatterTransport.scatter_outside row value axis layout absent]

/-- A localized Raw gate word acts on the exact live coordinates of the
whole physical frame. The outside coordinates remain in their reset state. -/
theorem localized_circuit_frame (dependencies : List Dependency) (layout : List Nat) (unique : layout.Nodup)
    (steps : List Step)
    (bounds : ∀ operation ∈ steps,
      (∀ control ∈ operation.controls, control.index < layout.length) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < layout.length))
    (amplitude : Nat → ℂ) :
    Semantics.RawAction.circuit dependencies (steps.map (QleisliKernel.Semantics.RawTrace.localize layout))
        (physicalColumn layout amplitude) =
      physicalColumn layout (Semantics.RawAction.circuit dependencies steps amplitude) := by
  classical
  funext row
  have targets := fun op held => (bounds op held).2
  rw [Semantics.RawAction.Locality.circuit_output dependencies row layout unique steps
    (fun op held => (bounds op held).1) targets]
  by_cases zero : OutsideZero layout row
  · have bounded : Qleisli.RawFiniteRows.BoundedEvent layout.length (.circuit layout.length steps) layout.length :=
      .circuit _ _ targets
    have same : Qleisli.RawFiniteRows.OnRows layout.length
        (Semantics.RawAction.Locality.pull row layout (physicalColumn layout amplitude)) amplitude := by
      intro input inside
      simp only [Semantics.RawAction.Locality.pull,physicalColumn,outside_scatter,zero,if_true]
      rw [Qleisli.RuntimeFiniteTargetScatter.gather_scatter row input layout unique inside]
    simpa only [Semantics.RawAction.event,physicalColumn,zero,if_true] using
      bounded.congr dependencies _ _ same (gather row layout) (gather_bound row layout)
  · have empty : Semantics.RawAction.Locality.pull row layout (physicalColumn layout amplitude) = fun _ => 0 := by
      funext input
      simp [Semantics.RawAction.Locality.pull,physicalColumn,outside_scatter,zero]
    rw [empty]
    simp only [physicalColumn,zero,if_false]
    simpa only [mul_zero] using Semantics.RawAction.circuit_scale dependencies steps amplitude 0 (gather row layout)

open QleisliKernel.Target.CanonicalOpenQasmResources (Instruction)

private theorem decoded_word_dependencies (dependencies : List Dependency) (gates : List Instruction)
    (amplitude : Nat → ℂ) :
    Semantics.RawAction.circuit [] (gates.map Instruction.step) amplitude =
      Semantics.RawAction.circuit dependencies (gates.map Instruction.step) amplitude := by
  induction gates generalizing amplitude with
  | nil => rfl
  | cons gate rest ih =>
    change Semantics.RawAction.circuit [] (rest.map Instruction.step) (Semantics.RawAction.step [] gate.step amplitude) =
      Semantics.RawAction.circuit dependencies (rest.map Instruction.step)
        (Semantics.RawAction.step dependencies gate.step amplitude)
    rw [ih]
    congr 1
    obtain ⟨gate,wires⟩ := gate
    cases gate <;> rfl

/-- The literal word selected by placement acts exactly as the original Raw
circuit in the ordered live frame, keeping all unused lines in their reset state. -/
theorem literal_circuit_preserves_frame {rootDependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior .original suffix)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Step}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : QleisliKernel.Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps]))
    (unique : occurrence.entry.locations.Nodup) (amplitude : Nat → ℂ) :
    let literal := (circuit.gates.drop occurrence.entry.gateIndex).take steps.length
    occurrence.exit.gateIndex = occurrence.entry.gateIndex+literal.length ∧
      Semantics.RawAction.circuit [] (literal.map Instruction.step)
          (physicalColumn occurrence.entry.locations amplitude) =
        physicalColumn occurrence.exit.locations (Semantics.RawAction.event rootDependencies (.circuit bits steps) amplitude) := by
  dsimp only
  obtain ⟨word,bounds,nextState,_,_⟩ := occurrence.literal_circuit occurs raw
  have length := congrArg List.length word
  simp only [List.length_map] at length
  rw [nextState]
  refine ⟨by rw [length],?_⟩
  rw [decoded_word_dependencies rootDependencies, word]
  exact localized_circuit_frame rootDependencies occurrence.entry.locations unique steps bounds amplitude

#print axioms localized_circuit_frame
#print axioms literal_circuit_preserves_frame

open QleisliKernel.Target.CanonicalOpenQasmPlacement (Decomposition)
open QleisliKernel.Target.CanonicalOpenQasmResources (decode)

private theorem register_width (bits : Nat) : width (QleisliKernel.Raw.registerBasis bits) = bits := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    cases bits with
    | zero => rfl
    | succ bits =>
      simp [QleisliKernel.Raw.registerBasis,QleisliKernel.Semantics.Raw.registerBasis,width] at ih ⊢
      omega

private theorem axis_bounds_of_matrix {dependencies bits steps matrix work left}
    (accepted : (QleisliKernel.Finite.circuitMatrix dependencies
      (QleisliKernel.Raw.circuit bits steps)).run work = (.ok matrix,left)) :
    ∀ operation ∈ steps,
      (∀ control ∈ operation.controls, control.index < bits) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < bits) := by
  have valid := (QleisliKernel.Finite.circuitMatrix_columns _ _ _ _ _ accepted).1
  have all : steps.all (QleisliKernel.Finite.stepValid dependencies bits) = true := by
    simpa only [QleisliKernel.Raw.circuit,register_width] using (Bool.and_eq_true_iff.mp valid).2
  intro operation member
  have stepValid := List.all_eq_true.mp all operation member
  have axesValid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp stepValid).1).2
  have bound := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp axesValid).1).2
  have within axis (held : axis ∈ operation.controls.map (·.index) ++
      QleisliKernel.Finite.targets operation.action) : axis < bits :=
    of_decide_eq_true (List.all_eq_true.mp bound axis held)
  exact ⟨fun control held => within _ (List.mem_append_left _ (List.mem_map_of_mem held)),
    fun axis held => within axis (List.mem_append_right _ held)⟩

private theorem lookup_layout {locations axes layout : List Nat}
    (placed : axes.mapM (fun axis => locations[axis]?) = some layout) :
    layout = axes.map (fun axis => (locations[axis]?).getD 0) := by
  induction axes generalizing layout with
  | nil => simpa using placed.symm
  | cons axis rest ih =>
    cases head : locations[axis]? with
    | none => simp [List.mapM_cons,head] at placed
    | some wire =>
      cases tail : rest.mapM (fun axis => locations[axis]?) with
      | none => simp [List.mapM_cons,head,tail] at placed
      | some suffix =>
        have equal : wire :: suffix = layout := by simpa [List.mapM_cons,head,tail] using placed
        rw [← equal,ih tail]
        simp [head]

/-- The actual decoded expansion applies the exact original local Raw action
in every spectator slice. The shared comparison matrix comes from the two
checked words. No physical-register matrix is reconstructed. -/
theorem decomposed_gate_slice {dependencies : List Dependency} {bytes : ByteArray}
    {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    {start count locations steps}
    (decoded : decode bytes = some circuit)
    (checked : Decomposition dependencies circuit start count locations steps)
    (amplitudes : Nat → ℂ) (row : Nat) :
    let localRaw := steps.map (QleisliKernel.Semantics.RawTrace.localize
      ((List.range locations.length).map checked.axes.idxOf))
    let literal := ((circuit.gates.drop start).take count).map Instruction.step
    Semantics.RawAction.circuit [] literal amplitudes row =
      Semantics.RawAction.circuit dependencies localRaw
        (Semantics.RawAction.Locality.pull row checked.layout amplitudes) (gather row checked.layout) := by
  dsimp only
  obtain ⟨originalWork,originalLeft,originalRun⟩ := checked.originalOperator
  obtain ⟨targetWork,targetLeft,targetRun⟩ := checked.targetOperator
  have originalAccepted : (QleisliKernel.Finite.circuitMatrix dependencies
      (QleisliKernel.Raw.circuit checked.axes.length (steps.map (QleisliKernel.Semantics.RawTrace.localize
        ((List.range locations.length).map checked.axes.idxOf))))).run originalWork =
      (.ok checked.matrix,originalLeft) := originalRun
  have bounds := axis_bounds_of_matrix targetRun
  have length : checked.layout.length = checked.axes.length := by
    rw [lookup_layout checked.placed,List.length_map]
  obtain ⟨_,_,shape⟩ := Qleisli.Raw.circuit_denotes _ _ _ _ _ _ targetRun
  have rows : checked.matrix.rows = 2^checked.axes.length :=
    congrArg QleisliKernel.Semantics.Exact.Matrix.rows shape
  have within : gather row checked.layout < checked.matrix.rows := by
    rw [rows,← length]
    exact gather_bound row checked.layout
  let joint := fun input (_ : Unit) => Semantics.RawAction.Locality.pull row checked.layout amplitudes input
  have target := Qleisli.Finite.circuitMatrix_action _ _ _ _ _ targetRun joint (gather row checked.layout) () within
  have original := Qleisli.Finite.circuitMatrix_action _ _ _ _ _ originalAccepted joint (gather row checked.layout) () within
  rw [← QleisliKernel.Target.CanonicalOpenQasmWorkspace.decoded_interval_roundtrip decoded checked.targetWord]
  have slice := Semantics.RawAction.Locality.circuit_output [] row checked.layout checked.declared.1 checked.actual
    (fun op held control member => length ▸ (bounds op held).1 control member)
    (fun op held axis member => length ▸ (bounds op held).2 axis member) amplitudes
  exact slice.trans (target.symm.trans original)

#print axioms decomposed_gate_slice

open QleisliKernel.Qirf.RuntimeScatterTransport (mappedAxes gather_mapped scatter_mapped scatter_gather scatter_outside)

open scoped Classical in
private theorem frame_slice (layout axes : List Nat) (unique : layout.Nodup)
    (bounds : ∀ axis ∈ axes, axis < layout.length) (amplitudes : Nat → ℂ) (row : Nat) :
    Semantics.RawAction.Locality.pull row (mappedAxes layout axes) (physicalColumn layout amplitudes) =
      fun input => if OutsideZero layout row then
        Semantics.RawAction.Locality.pull (gather row layout) axes amplitudes input else 0 := by
  classical
  funext input
  have scatterProjected := scatter_mapped row (gather row layout) input layout unique axes bounds
  rw [scatter_gather row layout unique] at scatterProjected
  have small := Qleisli.Finite.Pull.scatter_bound (gather row layout) layout.length input axes
    (gather_bound row layout) bounds
  have projected : gather (scatter row (mappedAxes layout axes) input) layout =
      scatter (gather row layout) axes input := by
    rw [scatterProjected,Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique small]
  have subset : mappedAxes layout axes ⊆ layout := by
    intro wire present
    obtain ⟨axis,member,rfl⟩ := List.mem_map.mp present
    simpa only [List.getElem?_eq_getElem (bounds axis member),Option.getD_some] using
      List.getElem_mem (bounds axis member) (l := layout)
  have agrees : OutsideZero layout (scatter row (mappedAxes layout axes) input) ↔ OutsideZero layout row := by
    simp only [OutsideZero]
    exact forall_congr' fun axis => imp_congr_right fun absent =>
      by rw [scatter_outside row input axis (mappedAxes layout axes) (fun held => absent (subset held))]
  simp only [Semantics.RawAction.Locality.pull,physicalColumn,agrees,projected]

/-- The exact decomposition applies over the entire placed frame. Every
spectator stays with its original joint amplitudes and every unused line is
still reset. This uses only the checked local matrix from the real gate slice. -/
theorem decomposed_preserves_frame {dependencies : List Dependency} {bytes : ByteArray}
    {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit} {start count locations steps}
    (decoded : decode bytes = some circuit)
    (checked : Decomposition dependencies circuit start count locations steps)
    (unique : locations.Nodup) (amplitudes : Nat → ℂ) :
    Semantics.RawAction.circuit [] (((circuit.gates.drop start).take count).map Instruction.step)
        (physicalColumn locations amplitudes) =
      physicalColumn locations (Semantics.RawAction.circuit dependencies steps amplitudes) := by
  classical
  funext row
  let localRaw := steps.map (QleisliKernel.Semantics.RawTrace.localize
    ((List.range locations.length).map checked.axes.idxOf))
  obtain ⟨inFrame,reindexed⟩ := checked.source_geometry
  have localized : localRaw.map (QleisliKernel.Semantics.RawTrace.localize checked.axes) = steps := reindexed
  have actual : checked.layout = mappedAxes locations checked.axes := lookup_layout checked.placed
  have selected : checked.axes.Nodup := List.Pairwise.of_map (fun axis => (locations[axis]?).getD 0)
    (fun _ _ different equal => different (congrArg (fun axis => (locations[axis]?).getD 0) equal))
    (actual ▸ checked.declared.1)
  have project : gather row checked.layout = gather (gather row locations) checked.axes := by
    have coordinates := gather_mapped row (gather row locations) locations unique checked.axes inFrame
    rwa [scatter_gather row locations unique,← actual] at coordinates
  have target := decomposed_gate_slice decoded checked (physicalColumn locations amplitudes) row
  change _ = Semantics.RawAction.circuit dependencies localRaw
    (Semantics.RawAction.Locality.pull row checked.layout (physicalColumn locations amplitudes)) (gather row checked.layout) at target
  obtain ⟨work,left,accepted⟩ := checked.originalOperator
  have ran : (QleisliKernel.Finite.circuitMatrix dependencies
    (QleisliKernel.Raw.circuit checked.axes.length localRaw)).run work = (.ok checked.matrix,left) := accepted
  have bounds := axis_bounds_of_matrix ran
  rw [target,project,actual,frame_slice locations checked.axes unique inFrame]
  by_cases reset : OutsideZero locations row
  · simp only [physicalColumn,reset,if_true]
    have source := Semantics.RawAction.Locality.circuit_output dependencies (gather row locations)
      checked.axes selected localRaw (fun op held => (bounds op held).1) (fun op held => (bounds op held).2) amplitudes
    rw [localized] at source
    exact source.symm
  · simp only [physicalColumn,reset,if_false]
    simpa only [mul_zero] using Semantics.RawAction.circuit_scale dependencies localRaw amplitudes 0
      (gather (gather row locations) checked.axes)

#print axioms decomposed_preserves_frame

private theorem checked_slice_length {circuit layout start count steps}
    (checked : QleisliKernel.Target.CanonicalOpenQasmWorkspace.interval circuit layout start count = some steps) :
    ((circuit.gates.drop start).take count).length = count := by
  have within := (QleisliKernel.Target.CanonicalOpenQasmWorkspace.interval_length checked).2
  change start+count ≤ circuit.gates.length at within
  simp only [List.length_take,List.length_drop]
  omega

/-- On a real decomposed occurrence, the Raw action and the full physical
register agree at the actual next placement state. The literal slice accounts
for precisely the performed gate count. -/
theorem decomposed_circuit_preserves_frame {rootDependencies original connected reserved initial final prior suffix count}
    {bytes : ByteArray} {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : decode bytes = some circuit)
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.decomposed count) suffix)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Step}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : QleisliKernel.Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps]))
    (unique : occurrence.entry.locations.Nodup) (amplitudes : Nat → ℂ) :
    let literal := (circuit.gates.drop occurrence.entry.gateIndex).take count
    occurrence.exit.gateIndex = occurrence.entry.gateIndex+literal.length ∧
      Semantics.RawAction.circuit [] (literal.map Instruction.step)
        (physicalColumn occurrence.entry.locations amplitudes) =
      physicalColumn occurrence.exit.locations
        (Semantics.RawAction.event rootDependencies (.circuit bits steps) amplitudes) := by
  dsimp only
  obtain ⟨⟨checked⟩,exit,_⟩ := occurrence.decomposed_circuit occurs raw
  rw [exit,checked_slice_length checked.targetWord]
  exact ⟨rfl,decomposed_preserves_frame decoded checked unique amplitudes⟩

#print axioms decomposed_circuit_preserves_frame

open QleisliKernel.Target.CanonicalOpenQasmPlacement (CircuitSpan readSpan_trace)

/-- The structural transitions retained by the original trace emit no gates.
Each actual circuit event contributes in order to the exact flattened action. -/
theorem span_action {original start frame offsets initial final events chunks}
    (trace : CircuitSpan original start frame offsets initial final events chunks)
    (dependencies : List Dependency) (amplitudes : Nat → ℂ) :
    Semantics.RawAction.events dependencies events amplitudes =
      Semantics.RawAction.circuit dependencies chunks.flatten amplitudes := by
  induction trace generalizing amplitudes with
  | empty => rfl
  | cons _ _ _ chunk _ ih =>
    cases chunk with
    | empty => exact ih amplitudes
    | gates bits steps =>
      simp only [List.singleton_append,List.flatten_cons]
      change Semantics.RawAction.events dependencies _
          (Semantics.RawAction.circuit dependencies steps amplitudes) = _
      rw [ih]
      simp only [Semantics.RawAction.circuit,List.foldl_append]

/-- An optimized interval with no designated scratch acts on the whole
placed frame exactly as the actual consecutive Raw events it replaces. -/
theorem optimized_decomposition_preserves_frame {rootDependencies original connected reserved initial final prior suffix rawCount gateCount}
    {bytes : ByteArray} {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : decode bytes = some circuit)
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.optimized rawCount gateCount []) suffix)
    (unique : occurrence.entry.locations.Nodup) (amplitudes : Nat → ℂ) :
    ∃ events chunks,
      CircuitSpan original occurrence.entry.rawIndex occurrence.entry.raw.frame (List.range rawCount)
        occurrence.entry.raw occurrence.exit.raw events chunks ∧
      let literal := (circuit.gates.drop occurrence.entry.gateIndex).take gateCount
      occurrence.exit.gateIndex = occurrence.entry.gateIndex+literal.length ∧
        Semantics.RawAction.circuit [] (literal.map Instruction.step)
          (physicalColumn occurrence.entry.locations amplitudes) =
        physicalColumn occurrence.exit.locations (Semantics.RawAction.events rootDependencies events amplitudes) := by
  obtain ⟨next,steps,computed,⟨checked⟩,exit⟩ := occurrence.optimized_decomposition
  obtain ⟨events,chunks,trace,flattened⟩ := readSpan_trace computed
  rw [exit]
  refine ⟨events,chunks,trace,?_⟩
  dsimp only
  rw [checked_slice_length checked.targetWord,span_action trace rootDependencies amplitudes,← flattened]
  exact ⟨rfl,decomposed_preserves_frame decoded checked unique amplitudes⟩

#print axioms span_action
#print axioms optimized_decomposition_preserves_frame

/-- An arbitrary list of distinct unused lines can be included in a local
frame as high zero coordinates, retaining the full physical amplitudes. -/
theorem extend_reset_frame (layout scratch : List Nat) (distinct : (layout ++ scratch).Nodup)
    (amplitudes : Nat → ℂ) :
    physicalColumn (layout ++ scratch)
      (Semantics.RawAction.event [] (.init0 layout.length) amplitudes) = physicalColumn layout amplitudes := by
  classical
  induction scratch using List.reverseRecOn with
  | nil =>
    funext row
    simp [Semantics.RawAction.event,physicalColumn,gather_bound]
  | append_singleton scratch wire ih =>
    rw [← List.append_assoc] at distinct ⊢
    obtain ⟨prefixUnique,_,apart⟩ := List.nodup_append.mp distinct
    have fresh : wire ∉ layout ++ scratch := fun inPrefix =>
      apart wire inPrefix wire (List.mem_singleton_self wire) rfl
    have widthBound : 2^layout.length ≤ 2^(layout ++ scratch).length :=
      Nat.pow_le_pow_right (by decide) (by simp)
    let zeroExtend := Semantics.RawAction.event [] (.init0 layout.length) amplitudes
    have clamp : Semantics.RawAction.event [] (.init0 (layout ++ scratch).length) zeroExtend = zeroExtend := by
      funext row
      by_cases data : row < 2^layout.length
      · have within := Nat.lt_of_lt_of_le data widthBound
        simp only [zeroExtend,Semantics.RawAction.event,data,within,if_true]
      · simp [zeroExtend,Semantics.RawAction.event,data]
    change physicalColumn ((layout ++ scratch) ++ [wire]) zeroExtend = _
    calc
      _ = physicalColumn ((layout ++ scratch) ++ [wire])
          (Semantics.RawAction.event [] (.init0 (layout ++ scratch).length) zeroExtend) := by rw [clamp]
      _ = physicalColumn (layout ++ scratch) zeroExtend := placed_init_zero _ _ fresh _
      _ = _ := ih prefixUnique

#print axioms extend_reset_frame

open QleisliKernel.Qirf.RuntimeScatterTransport (gather_at scatter_at)

private theorem gather_congr_bits (first second : Nat) (axes : List Nat)
    (same : ∀ axis ∈ axes, bit first axis = bit second axis) : gather first axes = gather second axes := by
  unfold gather
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair present
  have axis : pair.1 ∈ axes := by
    simpa only [List.zipIdx_map_fst] using (List.mem_map_of_mem (f := Prod.fst) present)
  change bit first pair.1 * 2^pair.2 = bit second pair.1 * 2^pair.2
  rw [same pair.1 axis]

private theorem gather_zero_iff (row : Nat) (axes : List Nat) :
    gather row axes = 0 ↔ ∀ axis ∈ axes, bit row axis = 0 := by
  constructor
  · intro zero axis present
    obtain ⟨index,bound,rfl⟩ := List.getElem_of_mem present
    rw [← gather_at row axes index bound,zero]
    simp [bit]
  · intro zeros
    unfold gather
    have same : (axes.zipIdx.map fun pair => bit row pair.1 * 2^pair.2) = axes.zipIdx.map (fun _ => 0) := by
      apply List.map_congr_left
      intro pair present
      have axis : pair.1 ∈ axes := by
        simpa only [List.zipIdx_map_fst] using (List.mem_map_of_mem (f := Prod.fst) present)
      rw [zeros pair.1 axis,Nat.zero_mul]
    rw [same]
    simp

private theorem outside_split {layout scratch : List Nat}
    (separate : ∀ axis ∈ scratch, axis ∉ layout) (row : Nat) :
    OutsideZero layout row ↔ OutsideZero (layout ++ scratch) row ∧ gather row scratch = 0 := by
  rw [gather_zero_iff]
  constructor
  · intro reset
    exact ⟨fun axis absent => reset axis (fun held => absent (List.mem_append_left _ held)),
      fun axis held => reset axis (separate axis held)⟩
  · rintro ⟨outside,zero⟩ axis absent
    by_cases temporary : axis ∈ scratch
    · exact zero axis temporary
    · exact outside axis (by simpa [absent] using temporary)

private theorem scatter_prefix_bit (row value axis : Nat) (first second : List Nat)
    (unique : (first ++ second).Nodup) (outside : axis ∉ second) :
    bit (scatter row (first ++ second) value) axis = bit (scatter row first value) axis := by
  by_cases found : axis ∈ first
  · obtain ⟨index,bound,rfl⟩ := List.getElem_of_mem found
    have full : index < (first ++ second).length := by simp; omega
    have same := scatter_at row value (first ++ second) unique index full
    rw [List.getElem_append_left bound] at same
    rw [same,scatter_at row value first (List.nodup_append.mp unique).1 index bound]
  · rw [scatter_outside row value _ _ (by simp [found,outside]),scatter_outside row value _ _ found]

private theorem mapped_frame_axes (layout axes : List Nat)
    (bounds : ∀ axis ∈ axes, axis < layout.length) : mappedAxes layout axes ⊆ layout := by
  intro wire present
  obtain ⟨axis,member,rfl⟩ := List.mem_map.mp present
  simpa only [List.getElem?_eq_getElem (bounds axis member),Option.getD_some] using
    List.getElem_mem (bounds axis member) (l := layout)

private theorem gather_scatter_frame (layout axes : List Nat) (unique : layout.Nodup)
    (bounds : ∀ axis ∈ axes, axis < layout.length) (row value : Nat) :
    gather (scatter row (mappedAxes layout axes) value) layout = scatter (gather row layout) axes value := by
  have same := scatter_mapped row (gather row layout) value layout unique axes bounds
  rw [scatter_gather row layout unique] at same
  rw [same,Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique
    (Qleisli.Finite.Pull.scatter_bound _ _ _ _ (gather_bound row layout) bounds)]

open scoped Classical in
/-- On the actual data-plus-scratch fibre, the physical frame is the logical
slice extended with a high zero coordinate for every scratch line. The
outside frame may be inspected at any row, including an invalid spectator. -/
theorem scratch_fibre (layout axes scratch : List Nat) (layoutUnique : layout.Nodup)
    (unique : (mappedAxes layout axes ++ scratch).Nodup)
    (bounds : ∀ axis ∈ axes, axis < layout.length)
    (separate : ∀ axis ∈ scratch, axis ∉ layout) (amplitudes : Nat → ℂ) (row input : Nat)
    (inside : input < 2^(axes.length + scratch.length)) :
    Semantics.RawAction.Locality.pull row (mappedAxes layout axes ++ scratch) (physicalColumn layout amplitudes) input =
      if OutsideZero (layout ++ scratch) row then
        Semantics.RawAction.event [] (.init0 axes.length)
          (Semantics.RawAction.Locality.pull (gather row layout) axes amplitudes) input else 0 := by
  classical
  let selected := mappedAxes layout axes
  let overwritten := scatter row (selected ++ scratch) input
  have length : selected.length = axes.length := List.length_map _
  have frameOutside : OutsideZero (layout ++ scratch) overwritten ↔ OutsideZero (layout ++ scratch) row := by
    simp only [OutsideZero]
    apply forall_congr'
    intro axis
    apply imp_congr_right
    intro absent
    have outside : axis ∉ selected ++ scratch := by
      intro found
      cases List.mem_append.mp found with
      | inl h => exact absent (List.mem_append_left _ (mapped_frame_axes layout axes bounds h))
      | inr h => exact absent (List.mem_append_right _ h)
    rw [scatter_outside row input axis _ outside]
  have view : gather overwritten layout = scatter (gather row layout) axes input := by
    rw [← gather_scatter_frame layout axes layoutUnique bounds row input]
    apply gather_congr_bits
    intro axis held
    apply scatter_prefix_bit row input axis selected scratch unique
    exact fun member => separate axis member held
  have coordinate : gather overwritten selected + 2^axes.length * gather overwritten scratch = input := by
    rw [← length,← gather_append]
    exact Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique (by
      simpa only [List.length_append,length] using inside)
  have low : gather overwritten selected < 2^axes.length := by
    rw [← length]
    exact gather_bound _ _
  have highZero : gather overwritten scratch = 0 ↔ input < 2^axes.length := by
    constructor
    · intro zero
      have same : gather overwritten selected = input := by simpa [zero] using coordinate
      simpa [same] using low
    · intro within
      by_contra nonzero
      have power : 2^axes.length ≤ 2^axes.length * gather overwritten scratch :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nonzero)
      omega
  have reset := (outside_split separate overwritten).trans (and_congr frameOutside highZero)
  change (if OutsideZero layout overwritten then amplitudes (gather overwritten layout) else 0) = _
  rw [reset,view]
  by_cases outside : OutsideZero (layout ++ scratch) row <;>
    by_cases small : input < 2^axes.length <;>
    simp [outside,small,Semantics.RawAction.Locality.pull,Semantics.RawAction.event]

/-- The exact checked zero encoding applies as a high-coordinate zero
extension on its finite domain, with every complex input coefficient intact. -/
theorem zero_encoding_action {bits scratch work left : Nat} {encoding : Encoding}
    (checked : (QleisliKernel.Raw.zeroEncoding bits scratch).run work = (.ok encoding,left))
    {R : Type} (joint : Nat → R → ℂ) (reference : R) (row : Nat) (within : row < 2^(bits+scratch)) :
    Qleisli.Semantics.Exact.action encoding.map joint row reference =
      Semantics.RawAction.event [] (.init0 bits) (fun col => joint col reference) row := by
  obtain ⟨_,_,before,after,mapped⟩ := QleisliKernel.Raw.zeroEncoding_value _ _ _ _ _ checked
  have cols := congrArg QleisliKernel.Semantics.Exact.Matrix.cols
    (QleisliKernel.Raw.mapping_value _ _ _ _ _ _ mapped)
  unfold Qleisli.Semantics.Exact.action
  rw [cols]
  simp only [Semantics.RawAction.event]
  calc
    _ = ((List.range (2^bits)).map (fun col => if col = row then joint col reference else 0)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro col member
      have bound := List.mem_range.mp member
      rw [Qleisli.Raw.mapping_meaning _ _ _ _ _ _ mapped row col within bound,List.getElem?_range bound]
      by_cases same : col = row <;> simp [same]
    _ = _ := by
      by_cases valid : row < 2^bits
      · rw [if_pos valid]
        simpa only [eq_comm] using Qleisli.Exact.range_delta_sum _ _ (fun col => joint col reference) valid
      · rw [if_neg valid]
        have zero : ((List.range (2^bits)).map (fun col => if col = row then joint col reference else 0)) =
            (List.range (2^bits)).map (fun _ => 0) := by
          apply List.map_congr_left
          intro col member
          have bound := List.mem_range.mp member
          have other : col ≠ row := by omega
          rw [if_neg other]
        rw [zero]
        simp

#print axioms scratch_fibre
#print axioms zero_encoding_action

open QleisliKernel.Target.CanonicalOpenQasmPlacement (Synthesis)

private theorem synthesis_target_bounds {dependencies circuit start count locations scratch reserved steps}
    (checked : Synthesis dependencies circuit start count locations scratch reserved steps) :
    ∀ operation ∈ checked.actual, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
      axis < checked.axes.length+scratch.length := by
  obtain ⟨encoding,_,work,left,_,accepted⟩ := checked.checkedEncoding
  let required : Contract := ⟨encoding,encoding,checked.logical⟩
  have ran : (QleisliKernel.Finite.check []
    (QleisliKernel.Raw.circuit (checked.axes.length+scratch.length) checked.actual) required required).run work =
      (.ok checked.physical,left) := accepted
  obtain ⟨_,_,_,_,_,_,read,_,_,_⟩ :=
    (QleisliKernel.Finite.check_conditions _ _ _ _ _ _ _ ran).2.2.2.2.2.2
  exact fun op held => (axis_bounds_of_matrix read op held).2

/-- The actual synthesized gates agree with the original circuit on the whole
register, including zero restoration of every scratch line. Spectator and
reference amplitudes are arbitrary throughout. -/
theorem synthesis_preserves_frame {dependencies : List Dependency} {bytes : ByteArray}
    {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit} {start count locations scratch reserved steps}
    (decoded : decode bytes = some circuit)
    (checked : Synthesis dependencies circuit start count locations scratch reserved steps) (amplitudes : Nat → ℂ) :
    Semantics.RawAction.circuit [] (((circuit.gates.drop start).take count).map Instruction.step)
        (physicalColumn locations amplitudes) =
      physicalColumn locations (Semantics.RawAction.circuit dependencies steps amplitudes) := by
  classical
  funext row
  obtain ⟨unique,width,supportUnique⟩ := Qleisli.WorkspaceTargetAction.synthesis_layout checked
  obtain ⟨locationsUnique,_,apart⟩ := List.nodup_append.mp checked.declared.1
  have fresh (axis : Nat) (member : axis ∈ scratch) : axis ∉ locations :=
    fun inFrame => apart axis inFrame axis member rfl
  obtain ⟨inFrame,reindexed⟩ := checked.source_geometry
  have physicalLayout : checked.layout = mappedAxes locations checked.axes := lookup_layout checked.placed
  have lowCoordinate : gather row checked.layout = gather (gather row locations) checked.axes := by
    have projected := gather_mapped row (gather row locations) locations locationsUnique checked.axes inFrame
    rwa [scatter_gather row locations locationsUnique,← physicalLayout] at projected
  let localRaw := steps.map (QleisliKernel.Semantics.RawTrace.localize
    ((List.range locations.length).map checked.axes.idxOf))
  have restoredSource : localRaw.map (QleisliKernel.Semantics.RawTrace.localize checked.axes) = steps := reindexed
  let localRow := gather row (checked.layout ++ scratch)
  let data := fun input => Semantics.RawAction.Locality.pull (gather row locations) checked.axes amplitudes input
  have packed : localRow = gather row checked.layout + 2^checked.axes.length * gather row scratch := by
    dsimp only [localRow]
    rw [gather_append,width]
  have within : localRow < 2^(checked.axes.length+scratch.length) := by
    simpa only [List.length_append,width,localRow] using gather_bound row (checked.layout ++ scratch)
  have sourceBound : gather row checked.layout < 2^checked.axes.length := by
    simpa only [width] using gather_bound row checked.layout
  have cleanRow : localRow < 2^checked.axes.length ↔ gather row scratch = 0 := by
    constructor
    · intro inside
      by_contra occupied
      have high : 2^checked.axes.length ≤ 2^checked.axes.length * gather row scratch :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero occupied)
      omega
    · intro clean
      simpa [packed,clean] using sourceBound
  have actual := Qleisli.WorkspaceTargetAction.physical_synthesis_slice decoded checked
    (fun input (_ : Unit) => physicalColumn locations amplitudes input) row ()
  change _ = Semantics.RawAction.circuit [] checked.actual
    (Semantics.RawAction.Locality.pull row (checked.layout ++ scratch) (physicalColumn locations amplitudes)) localRow at actual
  obtain ⟨zero,first,middle,mapped,returned⟩ := Qleisli.WorkspaceTargetAction.synthesis_action checked
  let bounded := Qleisli.RawFiniteRows.BoundedEvent.circuit (checked.axes.length+scratch.length) checked.actual
    (synthesis_target_bounds checked)
  have shape (input : Nat) (inRange : input < 2^(checked.axes.length+scratch.length)) :
      Semantics.RawAction.Locality.pull row (checked.layout ++ scratch) (physicalColumn locations amplitudes) input =
        if OutsideZero (locations ++ scratch) row then
          Semantics.RawAction.event [] (.init0 checked.axes.length) data input else 0 := by
    rw [physicalLayout]
    exact scratch_fibre locations checked.axes scratch locationsUnique (physicalLayout ▸ supportUnique)
      inFrame fresh amplitudes row input inRange
  rw [actual]
  by_cases outside : OutsideZero (locations ++ scratch) row
  · let joint := fun input (_ : Unit) => data input
    have same : Qleisli.RawFiniteRows.OnRows (checked.axes.length+scratch.length)
        (Semantics.RawAction.Locality.pull row (checked.layout ++ scratch) (physicalColumn locations amplitudes))
        (fun input => Qleisli.Semantics.Exact.action zero.map joint input ()) := by
      intro input inRange
      rw [shape input inRange,if_pos outside]
      exact (zero_encoding_action mapped joint () input inRange).symm
    have congruent := bounded.congr [] _ _ same localRow within
    simp only [Semantics.RawAction.event] at congruent
    rw [congruent,(returned Unit joint localRow () within).1]
    rw [zero_encoding_action mapped (fun col ref => Qleisli.Semantics.Exact.action checked.logical joint col ref) () localRow within]
    simp only [physicalColumn]
    have reset : OutsideZero locations row ↔ localRow < 2^checked.axes.length :=
      (outside_split fresh row).trans ⟨fun h => cleanRow.mpr h.2,fun h => ⟨outside,cleanRow.mp h⟩⟩
    rw [reset]
    by_cases clean : localRow < 2^checked.axes.length
    · have coordinate : localRow = gather row checked.layout := by simp [packed,cleanRow.mp clean]
      obtain ⟨work,left,ran⟩ := checked.originalOperator
      have originalAccepted : (QleisliKernel.Finite.circuitMatrix dependencies
        (QleisliKernel.Raw.circuit checked.axes.length localRaw)).run work = (.ok checked.logical,left) := ran
      obtain ⟨_,_,shape⟩ := Qleisli.Raw.circuit_denotes _ _ _ _ _ _ originalAccepted
      have rowBound : localRow < checked.logical.rows :=
        (congrArg QleisliKernel.Semantics.Exact.Matrix.rows shape).symm ▸ clean
      have logical := Qleisli.Finite.circuitMatrix_action _ _ _ _ _ originalAccepted joint localRow () rowBound
      have geometry := axis_bounds_of_matrix originalAccepted
      have source := Semantics.RawAction.Locality.circuit_output dependencies (gather row locations)
        checked.axes unique localRaw (fun op member => (geometry op member).1) (fun op member => (geometry op member).2) amplitudes
      rw [restoredSource] at source
      simp only [Semantics.RawAction.event,clean,if_true]
      exact logical.trans (by rw [coordinate,lowCoordinate]; exact source.symm)
    · simp [Semantics.RawAction.event,clean]
  · have same : Qleisli.RawFiniteRows.OnRows (checked.axes.length+scratch.length)
        (Semantics.RawAction.Locality.pull row (checked.layout ++ scratch) (physicalColumn locations amplitudes))
        (fun _ => 0) := by
      intro input inRange
      rw [shape input inRange,if_neg outside]
    have zero := bounded.congr [] _ _ same localRow within
    have invalid : ¬OutsideZero locations row := fun base => outside ((outside_split fresh row).mp base).1
    simp only [physicalColumn,invalid,if_false]
    exact zero.trans (by simpa only [Semantics.RawAction.event,mul_zero] using
      Semantics.RawAction.circuit_scale [] checked.actual amplitudes 0 localRow)

#print axioms synthesis_preserves_frame

/-- The successful occurrence binds the synthesized gates to its actual
original Raw step and both cursor positions, with all scratch restored. -/
theorem synthesized_circuit_preserves_frame {rootDependencies original connected reserved initial final prior suffix count scratch}
    {bytes : ByteArray} {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : decode bytes = some circuit)
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.synthesized count scratch) suffix)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Step}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : QleisliKernel.Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps]))
    (amplitudes : Nat → ℂ) :
    let literal := (circuit.gates.drop occurrence.entry.gateIndex).take count
    occurrence.exit.gateIndex = occurrence.entry.gateIndex+literal.length ∧
      Semantics.RawAction.circuit [] (literal.map Instruction.step)
        (physicalColumn occurrence.entry.locations amplitudes) =
      physicalColumn occurrence.exit.locations
        (Semantics.RawAction.event rootDependencies (.circuit bits steps) amplitudes) := by
  dsimp only
  obtain ⟨⟨checked⟩,exit,_⟩ := occurrence.synthesized_circuit occurs raw
  rw [exit,checked_slice_length checked.targetWord]
  exact ⟨rfl,synthesis_preserves_frame decoded checked amplitudes⟩

/-- A synthesized optimized interval preserves the action of its consecutive
original Raw events and returns every auxiliary coordinate to zero. -/
theorem optimized_synthesis_preserves_frame {rootDependencies original connected reserved initial final prior suffix rawCount gateCount scratch}
    {bytes : ByteArray} {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : decode bytes = some circuit)
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.optimized rawCount gateCount scratch) suffix) (usesScratch : scratch.isEmpty = false)
    (amplitudes : Nat → ℂ) :
    ∃ events chunks,
      CircuitSpan original occurrence.entry.rawIndex occurrence.entry.raw.frame (List.range rawCount)
        occurrence.entry.raw occurrence.exit.raw events chunks ∧
      let literal := (circuit.gates.drop occurrence.entry.gateIndex).take gateCount
      occurrence.exit.gateIndex = occurrence.entry.gateIndex+literal.length ∧
        Semantics.RawAction.circuit [] (literal.map Instruction.step)
          (physicalColumn occurrence.entry.locations amplitudes) =
        physicalColumn occurrence.exit.locations (Semantics.RawAction.events rootDependencies events amplitudes) := by
  obtain ⟨next,steps,computed,⟨checked⟩,exit⟩ := occurrence.optimized_synthesis usesScratch
  obtain ⟨events,chunks,trace,flattened⟩ := readSpan_trace computed
  rw [exit]
  refine ⟨events,chunks,trace,?_⟩
  dsimp only
  rw [checked_slice_length checked.targetWord,span_action trace rootDependencies amplitudes,← flattened]
  exact ⟨rfl,synthesis_preserves_frame decoded checked amplitudes⟩

#print axioms synthesized_circuit_preserves_frame
#print axioms optimized_synthesis_preserves_frame

open QleisliKernel.Target.CanonicalOpenQasmWorkspace (Checked decoded_interval_roundtrip)
open QleisliKernel.Qirf

private theorem workspace_gate_bounds {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {layout start count} (checked : Checked map target layout start count) :
    ∀ operation ∈ checked.gates,
      (∀ control ∈ operation.controls, control.index < layout.length) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < layout.length) := by
  obtain ⟨work,left,reported⟩ := checked.equation.checked
  obtain ⟨_,after,restored⟩ := QleisliKernel.Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ work left reported
  obtain ⟨_,_,_,_,_,_,_,_,_,read,_,_,_⟩ :=
    QleisliKernel.Raw.Workspace.check_conditions _ _ _ _ _ _ work after restored
  rw [checked.shape]
  exact axis_bounds_of_matrix read

/-- The decoded target slice executes the checked workspace word at the
original ordered data/scratch locations, on each actual spectator slice. -/
theorem physical_workspace_slice {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {layout start count} (checked : Checked map target layout start count)
    (amplitudes : Nat → ℂ) (row : Nat) :
    let literal := ((target.circuit.gates.drop start).take count).map Instruction.step
    Semantics.RawAction.circuit [] literal amplitudes row =
      Semantics.RawAction.circuit deps checked.gates
        (Semantics.RawAction.Locality.pull row layout amplitudes) (gather row layout) := by
  dsimp only
  rw [decoded_word_dependencies deps,← decoded_interval_roundtrip target.original checked.actualInterval]
  have bounds := workspace_gate_bounds checked
  exact Semantics.RawAction.Locality.circuit_output deps row layout checked.declared.1 checked.gates
    (fun op held => (bounds op held).1) (fun op held => (bounds op held).2) amplitudes

/-- The actual emitted slice and the independently read Raw workspace body
act identically on the same ordered physical and arbitrary reference slice. -/
theorem workspace_matches_raw_slice {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {layout start count} (checked : Checked map target layout start count)
    (amplitudes : Nat → ℂ) (row : Nat) :
    let word := ((target.circuit.gates.drop start).take count).map Instruction.step
    Semantics.RawAction.circuit [] word amplitudes row =
      Semantics.RawAction.circuit deps literal.emitted.steps
        (Semantics.RawAction.Locality.pull row layout amplitudes) (gather row layout) := by
  have within : gather row layout < 2^(original.layout.bits+1) := by
    rw [← checked.shape]
    exact gather_bound row layout
  exact (physical_workspace_slice checked amplitudes row).trans
    (Qleisli.WorkspaceTargetAction.decoded_action checked
      (fun input (_ : Unit) => Semantics.RawAction.Locality.pull row layout amplitudes input)
      (gather row layout) () within)

/-- The workspace equation of the actual decoded word carries the admitted
clean or dirty action on arbitrary reference columns. For dirty use the high
axis remains a spectator, including correlations with the other axes. -/
theorem workspace_local_restoration {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {layout start count} (checked : Checked map target layout start count)
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R)
    (within : row < 2^(original.layout.bits+1)) :
    let bits := original.layout.bits
    if event.fresh then
      Semantics.RawAction.circuit deps checked.gates (fun col => if col < 2^bits then joint col reference else 0) row =
        if row < 2^bits then Semantics.Exact.action original.logical.matrix joint row reference else 0
    else
      Semantics.RawAction.circuit deps checked.gates (fun col => joint col reference) row =
        Semantics.Exact.action original.logical.matrix
          (fun col ref => joint (scatter row (List.range bits) col) ref) (gather row (List.range bits)) reference := by
  have raw := Qleisli.RuntimeWorkspaceRestoration.literal_action literal joint row reference within
  dsimp only at raw ⊢
  cases fresh : event.fresh
  · simp only [fresh,Bool.false_eq_true,if_false] at raw ⊢
    exact (Qleisli.WorkspaceTargetAction.decoded_action checked joint row reference within).trans raw
  · simp only [fresh,if_true] at raw ⊢
    exact (Qleisli.WorkspaceTargetAction.decoded_action checked
      (fun col ref => if col < 2^original.layout.bits then joint col ref else 0) row reference within).trans raw

#print axioms physical_workspace_slice
#print axioms workspace_matches_raw_slice
#print axioms workspace_local_restoration

/-- Successful owner lookup yields the exact ordered subframe coordinates.
Each selected wire must be present before any physical default lookup could
apply. -/
theorem placed_workspace_axes {rawFrame locations wires placed : List Nat}
    (read : QleisliKernel.Target.CanonicalOpenQasmWorkspace.placedWires rawFrame locations wires = some placed) :
    wires ⊆ rawFrame ∧
      (∀ axis ∈ wires.map rawFrame.idxOf, axis < locations.length) ∧
      placed = mappedAxes locations (wires.map rawFrame.idxOf) := by
  let readWire := fun wire => if rawFrame.contains wire then locations[rawFrame.idxOf wire]? else none
  change wires.mapM readWire = some placed at read
  induction wires generalizing placed with
  | nil => simpa [mappedAxes] using read.symm
  | cons wire wires ih =>
    simp only [List.mapM_cons] at read
    by_cases member : wire ∈ rawFrame
    · have first : readWire wire = locations[rawFrame.idxOf wire]? := by simp [readWire,member]
      cases head : locations[rawFrame.idxOf wire]? with
      | none => simp [first,head,bind,Option.bind] at read
      | some physical =>
        cases tail : wires.mapM readWire with
        | none => simp [first,head,tail,bind,Option.bind] at read
        | some remaining =>
          have result : physical :: remaining = placed := by simp [first,head,tail,bind,Option.bind] at read; exact read
          obtain ⟨subset,inside,positions⟩ := ih tail
          refine ⟨?_,?_,?_⟩
          · intro next held
            rcases List.mem_cons.mp held with rfl | later
            · exact member
            · exact subset later
          · intro axis held
            simp only [List.map_cons,List.mem_cons] at held
            rcases held with rfl | later
            · exact (List.getElem?_eq_some_iff.mp head).1
            · exact inside _ later
          · rw [← result,positions]
            simp [mappedAxes,head]
    · simp [readWire,member,bind,Option.bind] at read

#print axioms placed_workspace_axes

open QleisliKernel.Target.CanonicalOpenQasmWorkspace (Placed)

/-- The dirty workspace acts on the original placed data and borrowed owner
inside the whole register. The untouched physical and reference coordinates
carry arbitrary joint amplitudes. -/
theorem dirty_workspace_frame {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {rawFrame locations start count} (checked : Placed map target rawFrame locations start count)
    (dirty : checked.freshScratch = none) (amplitudes : Nat → ℂ) :
    let axes := (map.selected.flatMap (·.port.wires)).map rawFrame.idxOf
    let word := ((target.circuit.gates.drop start).take count).map Instruction.step
    Semantics.RawAction.circuit [] word (physicalColumn locations amplitudes) =
      physicalColumn locations (Semantics.RawAction.embed axes
        (Semantics.RawAction.circuit deps literal.emitted.steps) amplitudes) := by
  classical
  dsimp only
  funext row
  let axes := (map.selected.flatMap (·.port.wires)).map rawFrame.idxOf
  obtain ⟨_,bounds,positions⟩ := placed_workspace_axes checked.boundOwners
  have full : checked.liveLayout ++ checked.freshScratch.toList = mappedAxes locations axes := by
    simp [dirty,positions,axes]
  have localRow : gather row (checked.liveLayout ++ checked.freshScratch.toList) = gather (gather row locations) axes := by
    have same := gather_mapped row (gather row locations) locations checked.declared.1 axes bounds
    rwa [scatter_gather row locations checked.declared.1,← full] at same
  have exactSlice := workspace_matches_raw_slice checked.body (physicalColumn locations amplitudes) row
  dsimp only at exactSlice
  rw [exactSlice,localRow,full,frame_slice locations axes checked.declared.1 bounds]
  by_cases outside : OutsideZero locations row
  · simp [axes,physicalColumn,outside,Semantics.RawAction.embed,Semantics.RawAction.Locality.pull]
  · simp only [physicalColumn,outside,if_false]
    simpa only [mul_zero] using Semantics.RawAction.circuit_scale deps literal.emitted.steps amplitudes 0
      (gather (gather row locations) axes)

#print axioms dirty_workspace_frame

/-- A clean workspace applies its checked logical matrix in the selected
owner order and returns the fresh physical line to zero. The claim covers
all physical coordinates of an arbitrary reference column. -/
theorem clean_workspace_frame {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {rawFrame locations start count} (checked : Placed map target rawFrame locations start count)
    {wire : Nat} (scratch : checked.freshScratch = some wire) (amplitudes : Nat → ℂ) :
    let axes := (map.selected.flatMap (·.port.wires)).map rawFrame.idxOf
    let word := ((target.circuit.gates.drop start).take count).map Instruction.step
    let logical := fun data row => Semantics.Exact.action original.logical.matrix (fun input (_ : Unit) => data input) row ()
    Semantics.RawAction.circuit [] word (physicalColumn locations amplitudes) =
      physicalColumn locations (Semantics.RawAction.embed axes logical amplitudes) := by
  classical
  dsimp only
  funext row
  let bits := original.layout.bits
  let axes := (map.selected.flatMap (·.port.wires)).map rawFrame.idxOf
  let localRow := gather row (checked.liveLayout ++ checked.freshScratch.toList)
  let data := Semantics.RawAction.Locality.pull (gather row locations) axes amplitudes
  obtain ⟨_,bounds,positions⟩ := placed_workspace_axes checked.boundOwners
  have full : checked.liveLayout ++ checked.freshScratch.toList = mappedAxes locations axes ++ [wire] := by
    rw [positions,scratch]
    rfl
  have dataWidth : checked.liveLayout.length = bits := by
    have shape := checked.body.shape
    simp only [scratch,Option.toList,List.length_append,List.length_singleton] at shape
    exact Nat.add_right_cancel shape
  have axesWidth : axes.length = bits := by
    simpa only [positions,mappedAxes,axes,List.length_map] using dataWidth
  have fresh : event.fresh = true := checked.scratchMode.symm.trans (by simp [scratch])
  have apart : ∀ axis ∈ [wire], axis ∉ locations := by
    intro axis member
    exact checked.scratchFree axis (by simpa [scratch] using member)
  have localBound : localRow < 2^(bits+1) := by
    dsimp only [localRow,bits]
    rw [← checked.body.shape]
    exact gather_bound _ _
  have packed : localRow = gather row checked.liveLayout + 2^bits * gather row [wire] := by
    dsimp only [localRow]
    rw [scratch,gather_append,dataWidth]
    rfl
  have low : gather row checked.liveLayout < 2^bits := by
    rw [← dataWidth]
    exact gather_bound _ _
  have cleanRow : localRow < 2^bits ↔ gather row [wire] = 0 := by
    constructor
    · intro small
      by_contra notReset
      have high : 2^bits ≤ 2^bits * gather row [wire] := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero notReset)
      omega
    · intro reset
      simpa [packed,reset] using low
  have logicalRow : gather row checked.liveLayout = gather (gather row locations) axes := by
    have read := gather_mapped row (gather row locations) locations checked.declared.1 axes bounds
    rwa [scatter_gather row locations checked.declared.1,← positions] at read
  have shape (input : Nat) (inside : input < 2^(bits+1)) :
      Semantics.RawAction.Locality.pull row (checked.liveLayout ++ checked.freshScratch.toList)
          (physicalColumn locations amplitudes) input =
        if OutsideZero (locations ++ [wire]) row then
          (if input < 2^bits then data input else 0) else 0 := by
    rw [full]
    have result := scratch_fibre locations axes [wire] checked.declared.1 (full ▸ checked.body.declared.1)
      bounds apart amplitudes row input (by simpa only [List.length_singleton,axesWidth] using inside)
    simpa only [Semantics.RawAction.event,axesWidth,data] using result
  have bounded : Qleisli.RawFiniteRows.BoundedEvent (bits+1) (.circuit (bits+1) checked.body.gates) (bits+1) := by
    refine .circuit _ _ fun op present axis member => ?_
    have inLayout := (workspace_gate_bounds checked.body op present).2 axis member
    rwa [← checked.body.shape]
  have emitted := physical_workspace_slice checked.body (physicalColumn locations amplitudes) row
  dsimp only at emitted
  rw [emitted]
  by_cases outside : OutsideZero (locations ++ [wire]) row
  · let joint := fun input (_ : Unit) => data input
    have same : Qleisli.RawFiniteRows.OnRows (bits+1)
        (Semantics.RawAction.Locality.pull row (checked.liveLayout ++ checked.freshScratch.toList) (physicalColumn locations amplitudes))
        (fun input => if input < 2^bits then joint input () else 0) := by
      intro input inside
      rw [shape input inside,if_pos outside]
    have congruent := bounded.congr deps _ _ same localRow localBound
    have restored := workspace_local_restoration checked.body joint localRow () localBound
    simp only [Semantics.RawAction.event] at congruent
    simp only [fresh,if_true] at restored
    change Semantics.RawAction.circuit deps checked.body.gates
        (fun col => if col < 2^bits then joint col () else 0) localRow =
      (if localRow < 2^bits then Semantics.Exact.action original.logical.matrix joint localRow () else 0) at restored
    have reset : OutsideZero locations row ↔ localRow < 2^bits :=
      (outside_split apart row).trans ⟨fun h => cleanRow.mpr h.2,fun h => ⟨outside,cleanRow.mp h⟩⟩
    rw [congruent,restored]
    simp only [physicalColumn,reset]
    by_cases zero : localRow < 2^bits
    · have coordinate : localRow = gather (gather row locations) axes := by
        rw [packed,cleanRow.mp zero,Nat.mul_zero,Nat.add_zero,logicalRow]
      simp only [zero,if_true,Semantics.RawAction.embed]
      rw [coordinate]
      rfl
    · simp only [zero,if_false]
  · have same : Qleisli.RawFiniteRows.OnRows (bits+1)
        (Semantics.RawAction.Locality.pull row (checked.liveLayout ++ checked.freshScratch.toList) (physicalColumn locations amplitudes))
        (fun _ => 0) := by
      intro input inside
      rw [shape input inside,if_neg outside]
    have zero := bounded.congr deps _ _ same localRow localBound
    have invalid : ¬OutsideZero locations row := fun reset => outside ((outside_split apart row).mp reset).1
    simp only [physicalColumn,invalid,if_false]
    exact zero.trans (by simpa only [Semantics.RawAction.event,mul_zero] using
      Semantics.RawAction.circuit_scale deps checked.body.gates amplitudes 0 localRow)

#print axioms clean_workspace_frame

end Qleisli.TerminalPlacement
