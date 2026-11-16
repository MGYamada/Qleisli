import TerminalPlacement.RawHistory
import TerminalPlacement.ProtectedWord
import Qleisli.StructuralComputedRestoration
import Qleisli.RuntimeTraceAxes
import Qleisli.RuntimeForestProduct
import Qleisli.RuntimeFiniteTargetScatter
import Qleisli.RawFiniteRows
import Qleisli.RawActionLinear
import Protocol.ExecutionView.CheckedQmatchV5
import Qleisli.RuntimeBasisOwnerGeometry
import Qleisli.RuntimeOwnerBindingFacts
import Qleisli.FiniteMatrixAction
import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.RawActionComposition
import Qleisli.RuntimeCallTraceProjection
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

private theorem reinstate_reset_frame (layout : List Nat) (unique : layout.Nodup)
    (row : Nat) (reset : OutsideZero layout row) : scatter 0 layout (gather row layout) = row := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have bits : bit (scatter 0 layout (gather row layout)) axis = bit row axis := by
    by_cases selected : axis ∈ layout
    · obtain ⟨index,bound,rfl⟩ := List.getElem_of_mem selected
      rw [scatter_at 0 (gather row layout) layout unique index bound,gather_at row layout index bound]
    · rw [scatter_outside 0 (gather row layout) axis layout selected,reset axis selected]
      simp [bit]
  simp only [bit] at bits
  rw [← Nat.toNat_testBit _ axis,← Nat.toNat_testBit row axis] at bits
  cases placed : (scatter 0 layout (gather row layout)).testBit axis <;>
    cases logical : row.testBit axis <;> simp_all

open scoped Classical in
/-- Sum over the complete physical terminal register and retain the two
arbitrary external reference coordinates. The exact reset-frame embedding
preserves the resulting measurement marginal, including off-diagonal entries
in the external reference. -/
theorem reference_marginal_on_placed_frame {R : Type} (layout : List Nat) (physicalBits : Nat)
    (unique : layout.Nodup) (declared : ∀ axis ∈ layout, axis < physicalBits)
    (physicalOutcome rawOutcome : Nat → Prop) [DecidablePred physicalOutcome] [DecidablePred rawOutcome]
    (sameOutcome : ∀ row, OutsideZero layout row → (physicalOutcome row ↔ rawOutcome (gather row layout)))
    (amplitudes : Nat → R → ℂ) (referenceLeft referenceRight : R) :
    (∑ row ∈ Finset.range (2^physicalBits),
      if physicalOutcome row then
        physicalColumn layout (fun logical => amplitudes logical referenceLeft) row *
          star (physicalColumn layout (fun logical => amplitudes logical referenceRight) row)
      else 0) =
    ∑ logical ∈ Finset.range (2^layout.length),
      if rawOutcome logical then amplitudes logical referenceLeft * star (amplitudes logical referenceRight) else 0 := by
  classical
  let full := Finset.range (2^physicalBits)
  let support := full.filter (OutsideZero layout)
  let term := fun row => if physicalOutcome row then
    physicalColumn layout (fun logical => amplitudes logical referenceLeft) row *
      star (physicalColumn layout (fun logical => amplitudes logical referenceRight) row) else 0
  change (∑ row ∈ full, term row) = _
  have discardZero : (∑ row ∈ support, term row) = ∑ row ∈ full, term row := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro row domain absent
    have reset : ¬OutsideZero layout row := fun yes => absent (Finset.mem_filter.mpr ⟨domain,yes⟩)
    simp [term,physicalColumn,reset]
  rw [← discardZero]
  refine Finset.sum_nbij' (fun row => gather row layout) (fun logical => scatter 0 layout logical) ?_ ?_ ?_ ?_ ?_
  · intro row _
    exact Finset.mem_range.mpr (gather_bound row layout)
  · intro logical _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Qleisli.Finite.Pull.scatter_bound 0 physicalBits logical layout
      (Nat.two_pow_pos _) declared),?_⟩
    intro axis unused
    rw [scatter_outside 0 logical axis layout unused]
    simp [bit]
  · intro row member
    exact reinstate_reset_frame layout unique row (Finset.mem_filter.mp member).2
  · intro logical member
    exact Qleisli.RuntimeFiniteTargetScatter.gather_scatter 0 logical layout unique (Finset.mem_range.mp member)
  · intro row member
    have reset := (Finset.mem_filter.mp member).2
    simp only [term,physicalColumn,reset,if_true,sameOutcome row reset]

#print axioms reference_marginal_on_placed_frame

open scoped Classical in
/-- Exact terminal marginal for the written classical result word of a
successful native readout. The raw indices in the right side are those of
its actual owner-consuming measurements. -/
theorem readout_reference_marginal {R : Type} {bytes capacity}
    {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {program : QleisliKernel.Semantics.Observation.Program}
    {state : QleisliKernel.Target.CanonicalOpenQasmPlacement.State}
    (checked : QleisliKernel.Target.CanonicalOpenQasmPlacement.Readout target program state)
    (declared : target.circuit.declares state.locations) (outcome : List Nat)
    (amplitudes : Nat → R → ℂ) (referenceLeft referenceRight : R) :
    (∑ row ∈ Finset.range (2^target.circuit.qubits),
      if target.circuit.measurements.map (bit row) = outcome then
        physicalColumn state.locations (fun logical => amplitudes logical referenceLeft) row *
          star (physicalColumn state.locations (fun logical => amplitudes logical referenceRight) row)
      else 0) =
    ∑ logical ∈ Finset.range (2^state.locations.length),
      if (target.circuit.measurements.map state.locations.idxOf).map (bit logical) = outcome then
        amplitudes logical referenceLeft * star (amplitudes logical referenceRight)
      else 0 := by
  exact reference_marginal_on_placed_frame state.locations target.circuit.qubits declared.1 declared.2
    (fun row => target.circuit.measurements.map (bit row) = outcome)
    (fun logical => (target.circuit.measurements.map state.locations.idxOf).map (bit logical) = outcome)
    (fun row _ => by simp only [checked.measurement_word declared.1 row]) amplitudes referenceLeft referenceRight

#print axioms readout_reference_marginal

open QleisliKernel.Qirf.RuntimeScatterTransport (gather_at scatter_at scatter_outside)
open QleisliKernel.Qirf.RuntimeNamedFrameAxes (wireLookup)
open QleisliKernel.Target.CanonicalOpenQasmPlacement (BasisLayout)

private theorem coordinate {axes : List Nat} {index axis : Nat}
    (row : Nat) (lookup : axes[index]? = some axis) : bit (gather row axes) index = bit row axis := by
  obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [gather_at row axes index inside,same]

private theorem bounded_bits_eq {left right bits : Nat} (leftBound : left < 2^bits)
    (rightBound : right < 2^bits) (below : ∀ axis < bits, bit left axis = bit right axis) : left = right := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have equal : bit left axis = bit right axis := by
    by_cases within : axis < bits
    · exact below axis within
    · have larger : 2^bits ≤ 2^axis := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt within)
      simp [bit,Nat.div_eq_of_lt (Nat.lt_of_lt_of_le leftBound larger),
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le rightBound larger)]
  simp only [bit] at equal
  rw [← Nat.toNat_testBit left axis,← Nat.toNat_testBit right axis] at equal
  cases leftBit : left.testBit axis <;> cases rightBit : right.testBit axis <;> simp_all

private theorem wiring_label {locations inputAxes outputAxes table final : List Nat}
    (layout : BasisLayout locations inputAxes outputAxes table final)
    (initialUnique : locations.Nodup) (input : Nat) (inputBound : input < 2^locations.length) :
    scatter input outputAxes (table[gather input inputAxes]?.getD 0) =
      gather input (final.map locations.idxOf) := by
  let label := gather input inputAxes
  have labelBound : label < table.length := layout.tableSize.symm ▸ gather_bound input inputAxes
  have code : table[label]?.getD 0 = gather label layout.inputForOutput := by
    have indexed : (table[label],label) ∈ table.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem labelBound)
    have checked := eq_of_beq (List.all_eq_true.mp layout.labels _ indexed)
    simpa only [List.getElem?_eq_getElem labelBound,Option.getD_some] using checked
  have width := layout.permutation.length_eq
  apply bounded_bits_eq (bits := locations.length)
  · exact Qleisli.Finite.Pull.scatter_bound _ _ _ _ inputBound layout.outputBounds
  · simpa only [List.length_map,width] using gather_bound input (final.map locations.idxOf)
  · intro axis inside
    have finalBound : axis < final.length := width.symm ▸ inside
    let wire := final[axis]
    have read : final[axis]? = some wire := List.getElem?_eq_getElem finalBound
    have reindex : (final.map locations.idxOf)[axis]? = some (locations.idxOf wire) := by
      rw [List.getElem?_map,read]
      rfl
    rw [coordinate input reindex]
    by_cases changed : axis ∈ outputAxes
    · obtain ⟨slot,slotBound,entry⟩ := List.getElem_of_mem changed
      have outputRead : outputAxes[slot]? = some axis :=
        (List.getElem?_eq_getElem slotBound).trans (congrArg some entry)
      have outWidth : outputAxes.length = inputAxes.length := layout.axes.length_eq
      have localWidth : layout.inputForOutput.length = inputAxes.length :=
        layout.ports.length_eq.trans List.length_range
      have portBound : slot < layout.inputForOutput.length := by omega
      let port := layout.inputForOutput[slot]
      have portRead : layout.inputForOutput[slot]? = some port := List.getElem?_eq_getElem portBound
      have portInside : port < inputAxes.length := List.mem_range.mp
        (layout.ports.mem_iff.mp (List.mem_of_getElem? portRead))
      let original := inputAxes[port]
      have inputRead : inputAxes[port]? = some original := List.getElem?_eq_getElem portInside
      have oldRead : locations[original]? = some wire :=
        (layout.selected outputRead portRead inputRead).symm.trans read
      have wireIn : wire ∈ locations := List.mem_of_getElem? oldRead
      have originalIndex : locations.idxOf wire = original :=
        (List.getElem?_inj (List.idxOf_lt_length_of_mem wireIn) initialUnique).mp
          ((wireLookup locations wireIn).trans oldRead.symm)
      rw [originalIndex]
      have changed := scatter_at input (table[label]?.getD 0) outputAxes layout.outputUnique slot slotBound
      rw [entry,code,coordinate label portRead,coordinate input inputRead] at changed
      simpa only [← code] using changed
    · have oldRead := (layout.spectator changed).symm.trans read
      have wireIn : wire ∈ locations := List.mem_of_getElem? oldRead
      have originalIndex : locations.idxOf wire = axis :=
        (List.getElem?_inj (List.idxOf_lt_length_of_mem wireIn) initialUnique).mp
          ((wireLookup locations wireIn).trans oldRead.symm)
      rw [scatter_outside _ _ _ _ changed,originalIndex]

private theorem wire_gather {locations final : List Nat} (permutation : final.Perm locations) (row : Nat) :
    gather (gather row locations) (final.map locations.idxOf) = gather row final := by
  apply bounded_bits_eq (bits := final.length)
  · simpa only [List.length_map] using gather_bound (gather row locations) (final.map locations.idxOf)
  · exact gather_bound row final
  · intro axis inside
    let wire := final[axis]
    have read : final[axis]? = some wire := List.getElem?_eq_getElem inside
    have inOld := permutation.mem_iff.mp (List.mem_of_getElem? read)
    have projected : (final.map locations.idxOf)[axis]? = some (locations.idxOf wire) := by
      rw [List.getElem?_map,read]
      rfl
    rw [coordinate _ projected,coordinate row (wireLookup locations inOld),coordinate row read]

/-- The checker-approved same-width table only changes the ordered placement.
Exact amplitudes and the physical register are preserved without any target gate. -/
theorem placed_same_width_basis {locations inputAxes outputAxes table final : List Nat}
    (layout : BasisLayout locations inputAxes outputAxes table final) (unique : locations.Nodup)
    (dependencies : List Dependency) (amplitudes : Nat → ℂ) :
    physicalColumn final (Semantics.RawAction.event dependencies
      (.liftBasis locations.length locations.length inputAxes outputAxes table) amplitudes) =
      physicalColumn locations amplitudes := by
  classical
  funext row
  have sameReset : OutsideZero final row ↔ OutsideZero locations row := by
    simp only [OutsideZero,layout.permutation.mem_iff]
  by_cases reset : OutsideZero locations row
  · simp only [physicalColumn,sameReset,reset,if_true,Semantics.RawAction.event,beq_iff_eq]
    let original := gather row locations
    have key (input : Nat) (inside : input < 2^locations.length) :
        scatter input outputAxes (table[gather input inputAxes]?.getD 0) = gather row final ↔
          original = input := by
      rw [wiring_label layout unique input inside,← wire_gather layout.permutation row]
      have partition : locations.Perm (final ++ []) := by simpa using layout.permutation.symm
      have equal := Qleisli.RuntimeCallTraceProjection.split_eq partition unique inside (gather_bound row locations)
      have emptyGather (n : Nat) : gather n [] = 0 := rfl
      exact (by simpa only [List.map_nil,emptyGather,eq_self,and_true] using equal.symm.trans eq_comm : _)
    calc
      _ = ((List.range (2^locations.length)).map fun input =>
          if original = input then amplitudes input else 0).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro input member
        simp only [key input (List.mem_range.mp member)]
      _ = amplitudes original := Qleisli.Exact.range_delta_sum _ _ _ (gather_bound row locations)
  · simp [physicalColumn,sameReset,reset]

#print axioms placed_same_width_basis

/-- The exact original basis occurrence changes the Raw coefficients and
physical placement together. The decoded target cursor stays unchanged. -/
theorem replayed_same_width_basis {dependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence dependencies original circuit connected reserved initial final prior .original suffix)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat}
    {inputAxes outputAxes table : List Nat}
    (source : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : QleisliKernel.Semantics.RawTrace.step occurrence.entry.raw operation =
      some (next,[.liftBasis bits bits inputAxes outputAxes table]))
    (unique : occurrence.entry.locations.Nodup) (amplitudes : Nat → ℂ) :
    occurrence.exit.gateIndex = occurrence.entry.gateIndex ∧
    physicalColumn occurrence.exit.locations (Semantics.RawAction.event dependencies
      (.liftBasis bits bits inputAxes outputAxes table) amplitudes) =
      physicalColumn occurrence.entry.locations amplitudes := by
  obtain ⟨⟨layout⟩,exit,width⟩ := occurrence.basis_layout source read
  refine ⟨congrArg (fun state => state.gateIndex) exit,?_⟩
  rw [width]
  exact placed_same_width_basis layout unique dependencies amplitudes

#print axioms replayed_same_width_basis


open QleisliKernel.Target.CanonicalOpenQasmPlacement (State)
open QleisliKernel.Target.CanonicalOpenQasmResources (Instruction)
open QleisliKernel.Semantics Qleisli.Semantics
open Qleisli.RuntimeAdjacentSlices (prefixSplit readOps_append)
/-- Executing the literal gate prefix of the decoded register, initialized in
its all-zero state. It is meaningful on the full register including every
reserved line. -/
noncomputable def resetPrefix (circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit) (stop : Nat) : Nat → ℂ :=
  RawAction.circuit [] ((circuit.gates.take stop).map Instruction.step)
    (fun physical => if physical = 0 then 1 else 0)

/-- Compose source and target slices at their actual ordered cursors. Each
extension reads the actual source operations between the Raw states and uses
the exact literal gates between their physical cursors. Its local equality
must hold on every input column, including entangled live data. -/
inductive PrefixAlignment (dependencies : List Dependency) (program : Observation.Program)
    (circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit) : State → List Event → Prop where
  | start (synthesis : List Nat) : PrefixAlignment dependencies program circuit {synthesis := synthesis} []
  | extend {entry exit : State} {earlier later : List Event} {rawCount gateCount : Nat}
      (earlierAligned : PrefixAlignment dependencies program circuit entry earlier)
      (sourceEnd : exit.rawIndex = entry.rawIndex+rawCount)
      (targetEnd : exit.gateIndex = entry.gateIndex+gateCount)
      (source : Observation.readOps 65 entry.raw ((program.operations.drop entry.rawIndex).take rawCount) =
        some (exit.raw,later.map Observation.Event.pure))
      (stepSound : ∀ amplitude,
        RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take gateCount).map Instruction.step)
          (physicalColumn entry.locations amplitude) =
        physicalColumn exit.locations (RawAction.events dependencies later amplitude)) :
      PrefixAlignment dependencies program circuit exit (earlier ++ later)

/-- An entire aligned prefix starts from the actual empty Raw interface and
reads the source operations up to its recorded Raw cursor. -/
theorem PrefixAlignment.read_prefix {dependencies program circuit state events}
    (trace : PrefixAlignment dependencies program circuit state events)
    (closed : program.inputs = []) :
    Observation.readOps 65 (RawTrace.initial program.inputs) (program.operations.take state.rawIndex) =
      some (state.raw,events.map Observation.Event.pure) := by
  induction trace with
  | start synthesis => rw [closed]; rfl
  | extend _ sourceEnd _ source _ ih =>
    rw [sourceEnd,prefixSplit,readOps_append 64,ih]
    simp [bind,Option.bind,source,List.map_append]

/-- Every gate in the literal target prefix is evaluated, in order, from the
register reset. The resulting amplitudes exactly embed the original closed Raw
prefix column, with no projection of live data or phase. -/
theorem PrefixAlignment.reset_column {dependencies program circuit state events}
    (trace : PrefixAlignment dependencies program circuit state events) :
    resetPrefix circuit state.gateIndex = physicalColumn state.locations
      (RawAction.events dependencies events (fun row => (Qleisli.Semantics.ObservingAction.initial []).operator row 0)) := by
  classical
  induction trace with
  | start synthesis =>
    funext row
    have iffZero : OutsideZero [] row ↔ row = 0 := by
      constructor
      · intro isZero
        apply Nat.eq_of_testBit_eq
        intro axis
        have zero := isZero axis (by simp)
        simp only [bit,← Nat.toNat_testBit] at zero
        cases tested : row.testBit axis <;> simp_all
      · intro zero
        subst row
        simp [OutsideZero,bit]
    change (if row = 0 then (1 : ℂ) else 0) = physicalColumn [] (fun i => (Qleisli.Semantics.ObservingAction.initial []).operator i 0) row
    rw [physicalColumn,iffZero,show gather row [] = 0 from rfl]
    by_cases zero : row = 0 <;> simp [zero,Qleisli.Semantics.ObservingAction.initial]
  | extend _ _ targetEnd _ stepSound ih =>
    rw [resetPrefix,targetEnd,prefixSplit,List.map_append]
    simp only [RawAction.circuit,List.foldl_append]
    change RawAction.circuit [] _ (resetPrefix circuit _) = _
    rw [ih,stepSound,Qleisli.RawActionComposition.events_append]

/-- The closed original prefix has one actual history, without classical or
hidden outcomes. Its column is precisely the one embedded in the decoded
physical register after the literal gate prefix. -/
theorem PrefixAlignment.closed_history {dependencies program circuit state events}
    (trace : PrefixAlignment dependencies program circuit state events)
    (closed : program.inputs = []) (noClassical : program.classicalInputs = []) (classical : List Bool) :
    ∃ history : Qleisli.Semantics.ObservingAction.History,
      Observation.readOps 65 (RawTrace.initial program.inputs) (program.operations.take state.rawIndex) =
        some (state.raw,events.map Observation.Event.pure) ∧
      Qleisli.Semantics.ObservingAction.run dependencies 65 (events.map Observation.Event.pure)
        (Qleisli.Semantics.ObservingAction.initial (program.classicalInputs.zip classical)) = some [history] ∧
      history.values = [] ∧ history.hidden = [] ∧
      resetPrefix circuit state.gateIndex = physicalColumn state.locations (fun row => history.operator row 0) := by
  rw [noClassical]
  exact ⟨Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies events (Qleisli.Semantics.ObservingAction.initial []),
    trace.read_prefix closed,
    Qleisli.RuntimeNamedThreePackedInstrument.run_pure dependencies 64 events (Qleisli.Semantics.ObservingAction.initial []),
    rfl,rfl,trace.reset_column⟩

#print axioms PrefixAlignment.read_prefix
#print axioms PrefixAlignment.reset_column
#print axioms PrefixAlignment.closed_history

/-- A successful actual routing match extends the physical prefix by its
literal SWAP. The original Raw reader and its event history stay at the
same cursor, with the same owners. -/
theorem PrefixAlignment.extend_route {dependencies program circuit connected reserved initial final prior suffix events}
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved
      initial final prior .route suffix)
    (earlier : PrefixAlignment dependencies program circuit occurrence.entry events) :
    PrefixAlignment dependencies program circuit occurrence.exit events := by
  obtain ⟨first,second,distinct,gate,_,exit⟩ := occurrence.route
  have slice : (circuit.gates.drop occurrence.entry.gateIndex).take 1 = [⟨.swap,[first,second]⟩] := by
    obtain ⟨inside,found⟩ := List.getElem?_eq_some_iff.mp gate
    rw [List.take_one_drop_eq_of_lt_length inside]
    exact congrArg (fun instruction => [instruction]) found
  have aligned := PrefixAlignment.extend (later := []) (rawCount := 0) (gateCount := 1)
    (exit := occurrence.exit) earlier
    (by rw [exit]; rfl) (by rw [exit]) (by rw [exit]; rfl)
  rw [List.append_nil] at aligned
  apply aligned
  intro amplitude
  rw [slice,exit]
  exact placed_literal_swap ⟨first,second⟩ distinct occurrence.entry.locations amplitude

#print axioms PrefixAlignment.extend_route

open QleisliKernel.Qirf.RuntimeOwnerMap (Binding)
open QleisliKernel.Target.CanonicalOpenQasmPlacement (BoundSegment Segment dirty_packet_source)
open QleisliKernel.Semantics.Raw (Port)

private theorem ordered_workspace_ports {full first second : List Binding}
    (unique : (full.map (fun binding => binding.owner.ordinal)).Nodup)
    (firstInside : first ⊆ full) (secondInside : second ⊆ full)
    (ordered : first.map (·.owner) = second.map (·.owner)) : first = second := by
  induction first generalizing second with
  | nil => simpa using ordered
  | cons head tail ih =>
    cases second with
    | nil => simp at ordered
    | cons first rest =>
      obtain ⟨sameOwner,sameTail⟩ := List.cons.inj ordered
      have same := Qleisli.RuntimeOwnerTransitionAction.map_unique
        (fun binding : Binding => binding.owner.ordinal) full unique
        head (firstInside List.mem_cons_self) first (secondInside List.mem_cons_self)
        (congrArg (·.ordinal) sameOwner)
      rw [same,ih (fun _ member => firstInside (List.mem_cons_of_mem _ member))
        (fun _ member => secondInside (List.mem_cons_of_mem _ member)) sameTail]

/-- Bind the original packet's data and borrowed owner to the same ordered
ports that the native placement used, retaining complete owner identities. -/
private theorem dirty_workspace_ports {program : Observation.Program} (segment : Segment program)
    (dirty : segment.event.fresh = false)
    {scratch : RuntimePrimitiveSource.PortAt segment.event.scratch segment.sourceBefore.bindings}
    (_ : segment.literal.scratch = some scratch) :
    segment.map.selected.map (·.port) = [segment.literal.input.port,scratch.port] := by
  let expected : List Binding := [⟨segment.event.input,segment.literal.input.port⟩,
    ⟨segment.event.scratch,scratch.port⟩]
  let frame := segment.literal.frame
  have ordinals : (frame.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    simpa only [← frame.ordered,List.map_map,Function.comp_def] using frame.ownersDistinct
  have before : expected ⊆ frame.bindings := by
    intro binding member
    rw [segment.literal.sameFrame]
    simp [expected] at member
    rcases member with rfl | rfl
    · exact Qleisli.RuntimeBasisOwnerGeometry.selected_binding segment.literal.input
    · exact Qleisli.RuntimeBasisOwnerGeometry.selected_binding scratch
  have after : segment.map.selected ⊆ frame.bindings := fun _ member =>
    segment.map.inputPartition.mem_iff.mp (List.mem_append_left _ member)
  have ordered : segment.map.selected.map (·.owner) = expected.map (·.owner) := by
    rw [segment.map.orderedInput]
    simp [RuntimeWorkspace.inputOwners,dirty,expected]
  rw [ordered_workspace_ports ordinals after before ordered]
  rfl

private def withoutPort (state : Interface) (token : Nat) : Interface :=
  {state with live := state.live.filter (fun port => port.token != token)}

private theorem workspace_take (state : Interface) (port : Port)
    (unique : (state.live.map (·.token)).Nodup) (present : port ∈ state.live) :
    RawTrace.take state port.token = some (port,withoutPort state port.token) := by
  simp only [RawTrace.take,RuntimeNamedFrameAxes.tokenLookup state.live port unique present,bind,Option.bind]
  rfl

/-- The exact dirty packet is join, literal unitary on its ordered joined
wires, then split. The verified original ownership run excludes a spectator
with the intermediate joined token. -/
private theorem dirty_packet_trace {before after : Ownership.State} {data auxiliary : Port}
    {joined packed output returned bits : Nat} {steps : List Step} {traced : RawTrace.Prepared}
    (distinct : data.token ≠ auxiliary.token) (dataIn : data ∈ before.live) (auxiliaryIn : auxiliary ∈ before.live)
    (run : Ownership.Run before
      [.pure (.join data.token auxiliary.token joined), .pure (.applyUnitary joined packed steps),
        .pure (.split packed output returned bits)] after)
    (read : RawTrace.interval before.interface
      [.join data.token auxiliary.token joined,.applyUnitary joined packed steps,.split packed output returned bits] = some traced) :
    traced.events = [.circuit before.frame.length
      (steps.map (RawTrace.localize (RawTrace.axes before.interface (data.wires ++ auxiliary.wires))))] := by
  have valid := run.initial_valid
  let first := withoutPort before.interface data.token
  let remaining := withoutPort first auxiliary.token
  have takeData : RawTrace.take before.interface data.token = some (data,first) :=
    workspace_take before.interface data valid.owners dataIn
  have another : auxiliary ∈ first.live := List.mem_filter.mpr ⟨auxiliaryIn, bne_iff_ne.mpr distinct.symm⟩
  have unique : (first.live.map (·.token)).Nodup :=
    List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) valid.owners
  have takeScratch : RawTrace.take first auxiliary.token = some (auxiliary,remaining) :=
    workspace_take first auxiliary unique another
  let wires := data.wires ++ auxiliary.wires
  let joinedPort : Port := ⟨joined,wires,wires.length⟩
  let joinedState := RawTrace.insert remaining joined wires
  have readJoin : RawTrace.step before.interface (.join data.token auxiliary.token joined) =
      some (joinedState,[]) := by
    simp only [RawTrace.step,takeData,takeScratch,bind,Option.bind]
    rfl
  cases run with
  | cons _ _ mid _ _ _ head tail =>
    cases head with
    | pure _ _ _ joinRule =>
      obtain ⟨_,checkedJoin⟩ := joinRule.action
      have actualJoin : mid.interface = joinedState :=
        congrArg Prod.fst (Option.some.inj (checkedJoin.symm.trans readJoin))
      have joinedUnique := tail.initial_valid.owners
      change (mid.interface.live.map (·.token)).Nodup at joinedUnique
      rw [actualJoin] at joinedUnique
      have joinedHeld : joinedPort ∈ joinedState.live := List.mem_append_right _ List.mem_cons_self
      have takeJoined := workspace_take joinedState joinedPort joinedUnique joinedHeld
      let pending := withoutPort joinedState joined
      let next := RawTrace.insert pending packed wires
      let events : List Event := [.circuit before.frame.length
        (steps.map (RawTrace.localize (RawTrace.axes before.interface wires)))]
      have readApply : RawTrace.step joinedState (.applyUnitary joined packed steps) = some (next,events) := by
        change _ = some (next,events)
        have token : joinedPort.token = joined := rfl
        rw [token] at takeJoined
        simp only [RawTrace.step,takeJoined,bind,Option.bind]
        rfl
      simp only [RawTrace.interval,List.foldlM_cons,List.foldlM_nil,RawTrace.advance,
        readJoin,readApply,bind,Option.bind,pure,List.nil_append] at read
      cases takes : RawTrace.take next packed with
      | none => simp [RawTrace.step,takes] at read
      | some pair =>
        obtain ⟨port,last⟩ := pair
        simp [RawTrace.step,takes] at read
        exact (congrArg RawTrace.Prepared.events read).symm

/-- Lift the original dirty workspace packet to the actual physical gate
interval. The native placement and original ownership proof are used for
that same source cursor and the same ordered data and borrowed owner. -/
theorem PrefixAlignment.extend_dirty_workspace {program : Observation.Program} {segment : Segment program}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {dependencies connected reserved previous entry earlier}
    (bound : BoundSegment segment dependencies target connected reserved previous entry)
    (sameDependencies : segment.dependencies = dependencies)
    (dirty : bound.placed.freshScratch = none)
    {start done_ : Ownership.State}
    (originalEntry : start.interface = entry.raw)
    (valid : Ownership.Run start ((program.operations.drop entry.rawIndex).take segment.length) done_)
    (aligned : PrefixAlignment dependencies program target.circuit entry earlier) :
    ∃ events, PrefixAlignment dependencies program target.circuit
      ⟨bound.after,entry.locations,entry.rawIndex+segment.length,entry.gateIndex+segment.count,entry.synthesis⟩
      (earlier ++ events) := by
  obtain ⟨original,trace,traceRead,traceAfter,_⟩ := bound.original_workspace_trace
  have fresh : segment.event.fresh = false := by simpa [dirty] using bound.placed.scratchMode.symm
  obtain ⟨work,left,readPacket⟩ := segment.literal.emittedRead
  rw [fresh] at readPacket
  obtain ⟨auxiliary,joined,packed,returned,rawScratch,_,packet⟩ := dirty_packet_source readPacket
  cases scratchRead : segment.literal.scratch with
  | none => simp [scratchRead] at rawScratch
  | some scratch =>
    have auxId : auxiliary = scratch.port.token := by simpa [scratchRead] using rawScratch.symm
    subst auxiliary
    -- The packet reader supplies the decoded operation list as Obs.pure;
    -- recover the Raw list via injectivity of map and rewrite both original runs.
    have rawOperations : segment.literal.operations =
        [.join segment.literal.input.port.token scratch.port.token joined,
          .applyUnitary joined packed segment.literal.emitted.steps,
          .split packed segment.literal.emitted.dataOut returned segment.original.layout.bits] := by
      apply List.map_injective_iff.mpr (fun _ _ equal => Observation.Op.pure.inj equal)
      exact segment.literal.originalOperations.symm.trans packet
    have ports := dirty_workspace_ports segment fresh scratchRead
    have lookup := bound.selected
    change PureInterval.portsOf entry.raw.live
      ((segment.map.selected.map (·.port)).map (·.token)) = some (segment.map.selected.map (·.port)) at lookup
    rw [ports,← originalEntry] at lookup
    have selected := RuntimeNamedFrameAxes.selectedPorts _ _ _ lookup
    have allTokens := (segment.map.inputPartition.map (fun binding => binding.port.token)).nodup_iff.mpr
      segment.literal.frame.tokensDistinct
    have apart : segment.literal.input.port.token ≠ scratch.port.token := by
      have pair : ((segment.map.selected.map Binding.port).map (·.token)).Nodup := by
        rw [List.map_map]
        simp only [List.map_append] at allTokens
        exact (List.nodup_append.mp allTokens).1
      rw [ports] at pair
      simpa using pair
    rw [original,rawOperations] at valid
    have canonicalRead := traceRead
    rw [← originalEntry,rawOperations] at canonicalRead
    have dataIn : segment.literal.input.port ∈ start.live := selected.1 (by simp)
    have auxIn : scratch.port ∈ start.live := selected.1 (by simp)
    have events := dirty_packet_trace apart dataIn auxIn valid canonicalRead
    have source := Qleisli.RuntimeAdjacentSlices.readOps_pure 64 _ _ _ traceRead
    rw [← original,traceAfter] at source
    refine ⟨trace.events,.extend (rawCount := segment.length) (gateCount := segment.count) aligned rfl rfl source ?_⟩
    intro amplitude
    change RawAction.circuit [] (((target.circuit.gates.drop entry.gateIndex).take segment.count).map Instruction.step)
        (physicalColumn entry.locations amplitude) = physicalColumn entry.locations (RawAction.events dependencies trace.events amplitude)
    have targetColumn := dirty_workspace_frame bound.placed dirty amplitude
    dsimp only at targetColumn
    rw [← sameDependencies,events,originalEntry]
    let axes := RawTrace.axes entry.raw (segment.literal.input.port.wires ++ scratch.port.wires)
    have selectedAxes : (segment.map.selected.flatMap (·.port.wires)).map entry.raw.frame.idxOf = axes := by
      rw [← List.flatMap_map Binding.port]
      simp [ports,axes,RawTrace.axes]
    rw [selectedAxes] at targetColumn
    rw [targetColumn]
    congr 1
    funext row
    simp only [RawAction.events,List.foldl_cons,List.foldl_nil,RawAction.event]
    obtain ⟨_,_,placed⟩ := placed_workspace_axes bound.placed.boundOwners
    rw [selectedAxes] at placed
    have liveUnique := bound.placed.body.declared.1
    simp only [dirty,Option.toList_none,List.append_nil,placed] at liveUnique
    have axesUnique : axes.Nodup := List.Nodup.of_map _ liveUnique
    have actualWidth := bound.placed.body.shape
    simp only [dirty,Option.toList_none,List.append_nil,placed,mappedAxes,List.length_map] at actualWidth
    obtain ⟨before,after,checked⟩ := segment.literal.equation.checked
    obtain ⟨_,middle,originalChecked⟩ := QleisliKernel.Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ before after checked
    obtain ⟨_,_,_,_,_,_,_,_,_,matrix,_,_,_⟩ :=
      QleisliKernel.Raw.Workspace.check_conditions _ _ _ _ _ _ before middle originalChecked
    have bounds := axis_bounds_of_matrix matrix
    change RawAction.embed axes (RawAction.circuit segment.dependencies segment.literal.emitted.steps) amplitude row =
      RawAction.circuit segment.dependencies (segment.literal.emitted.steps.map (RawTrace.localize axes)) amplitude row
    exact (RawAction.Locality.circuit_output segment.dependencies row axes axesUnique segment.literal.emitted.steps
      (fun step held control member => by rw [actualWidth]; exact (bounds step held).1 control member)
      (fun step held axis member => by rw [actualWidth]; exact (bounds step held).2 axis member) amplitude).symm

#print axioms PrefixAlignment.extend_dirty_workspace

/-- In a workspace packet, the zero predicate table reads as the identity
on every surrounding frame. Both the forward and inverse have this action. -/
private theorem zero_workspace_compute (dependencies : List Dependency)
    (sourceBits dataBits scratchBits size : Nat) (ψ : Nat → ℂ) :
    RawAction.step dependencies
      (QleisliKernel.Raw.computeStep sourceBits dataBits scratchBits (List.replicate size 0)) ψ = ψ := by
  let width := dataBits+scratchBits
  let axes := List.range width
  let terms := List.range (2^width)
  have zeroEntry (count index : Nat) : ((List.replicate count (0 : Nat))[index]?).getD 0 = 0 := by
    rw [List.getElem?_replicate]
    split <;> rfl
  have permutation : (terms.map fun label =>
      label ^^^ (((List.replicate size (0 : Nat))[label % 2^sourceBits]?).getD 0 * 2^dataBits)) = terms := by
    simp only [zeroEntry,Nat.zero_mul,Nat.xor_zero]
    exact List.map_id _
  funext row
  unfold QleisliKernel.Raw.computeStep QleisliKernel.Semantics.Raw.computeStep
  change RawAction.step dependencies ⟨[],.monomial axes
    (terms.map fun label => label ^^^ (((List.replicate size (0 : Nat))[label % 2^sourceBits]?).getD 0 * 2^dataBits))
    (List.replicate (2^width) 0)⟩ ψ row = _
  rw [permutation]
  simp only [RawAction.step,enabled,List.all_nil,Bool.not_true,Bool.false_eq_true,if_false]
  have same : ((List.range terms.length).map fun input =>
      if terms[input]? == some (gather row axes) then
        ψ (scatter row axes input) * Qleisli.Semantics.Finite.phase
          (((List.replicate (2^width) (0 : Nat))[input]?).getD 0) else 0).sum =
      (terms.map fun input => if gather row axes = input then ψ (scatter row axes input) else 0).sum := by
    have length : terms.length = 2^width := List.length_range
    rw [length]
    apply Qleisli.Exact.sum_map_congr
    intro input member
    have within : input < 2^width := List.mem_range.mp member
    have termAt : terms[input]? = some input := List.getElem?_range within
    rw [termAt,zeroEntry]
    have trivialPhase : Qleisli.Semantics.Finite.phase 0 = 1 := rfl
    by_cases hit : gather row axes = input
    · rw [hit]
      simp only [beq_self_eq_true,if_true,trivialPhase,mul_one]
    · have different : (some input == some (gather row axes)) = false :=
        beq_false_of_ne (fun equal => hit (Option.some.inj equal).symm)
      simp only [different,Bool.false_eq_true,if_false,hit]
  rw [same]
  have small : gather row axes < 2^width := by simpa [axes] using gather_bound row axes
  rw [Qleisli.Exact.range_delta_sum _ _ _ small,scatter_gather row axes List.nodup_range]

/-- The actual single certified-compute event of the clean packet uses the
checked data-frame logical matrix. Its zero-table forward/inverse operations
are eliminated at the coefficient level, independently of the gate slice. -/
theorem clean_workspace_raw_event {sources caller deps program block sourceStart sourceCount sourceBefore}
    {event : QleisliKernel.SourceTypes.SourceRuntimeContext.WorkspaceEvent sources caller}
    {events : List (QleisliKernel.SourceTypes.SourceRuntimeContext.Event sources caller)}
    {original : RuntimeWorkspace.Original event events}
    {sourceInterval : @RuntimeInterval.Checked deps program block sourceStart sourceCount}
    (literal : RuntimeWorkspace.Literal original sourceInterval sourceBefore)
    (fresh : event.fresh = true) (bits sourceBits : Nat) (axes : List Nat) (width : axes.length = original.layout.bits)
    (logicalSteps : List Step) (amplitude : Nat → ℂ) :
    RawAction.event deps
      (.computed bits axes sourceBits 1 (List.replicate (2^original.layout.bits) 0) literal.emitted.steps logicalSteps)
      amplitude =
    RawAction.embed axes (fun data row => Semantics.Exact.action original.logical.matrix
      (fun input (_ : Unit) => data input) row ()) amplitude := by
  funext row
  let input : Nat → Unit → ℂ := fun localIndex _ => amplitude (scatter row axes localIndex)
  let compute := QleisliKernel.Raw.computeStep sourceBits axes.length 1
    (List.replicate (2^original.layout.bits) 0)
  change RawAction.circuit deps ([compute] ++ literal.emitted.steps ++ [compute])
      (fun index => if index < 2^axes.length then input index () else 0) (gather row axes) =
    Semantics.Exact.action original.logical.matrix input (gather row axes) ()
  have dropZero (ψ : Nat → ℂ) : RawAction.circuit deps ([compute] ++ literal.emitted.steps ++ [compute]) ψ =
      RawAction.circuit deps literal.emitted.steps ψ := by
    simp only [RawAction.circuit,List.foldl_append,List.foldl_cons,List.foldl_nil,compute,zero_workspace_compute]
  rw [dropZero,width]
  have low : gather row axes < 2^original.layout.bits := width ▸ gather_bound row axes
  have full : gather row axes < 2^(original.layout.bits+1) :=
    Nat.lt_of_lt_of_le low (Nat.pow_le_pow_right (by decide) (by omega))
  have restored := Qleisli.RuntimeWorkspaceRestoration.literal_action literal input (gather row axes) () full
  simpa only [fresh,if_true,low] using restored

#print axioms clean_workspace_raw_event

private theorem clean_workspace_ports {program : Observation.Program} (segment : Segment program)
    (fresh : segment.event.fresh = true) :
    segment.map.selected.map (·.port) = [segment.literal.input.port] := by
  let expected : List Binding := [⟨segment.event.input,segment.literal.input.port⟩]
  let frame := segment.literal.frame
  have ordinals : (frame.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    simpa only [← frame.ordered,List.map_map,Function.comp_def] using frame.ownersDistinct
  have before : expected ⊆ frame.bindings := by
    intro binding member
    rw [segment.literal.sameFrame]
    obtain rfl := List.mem_singleton.mp member
    exact Qleisli.RuntimeBasisOwnerGeometry.selected_binding segment.literal.input
  have after : segment.map.selected ⊆ frame.bindings := fun _ member =>
    segment.map.inputPartition.mem_iff.mp (List.mem_append_left _ member)
  have ordered : segment.map.selected.map (·.owner) = expected.map (·.owner) := by
    rw [segment.map.orderedInput]
    simp [RuntimeWorkspace.inputOwners,fresh,expected]
  rw [ordered_workspace_ports ordinals after before ordered]
  rfl

set_option maxHeartbeats 800000 in
/-- The checked clean workspace consumes the exact original certified-compute
packet, including its private zero-table scratch. The original Raw column and
literal OpenQASM gate interval both use the same checked logical matrix. -/
theorem PrefixAlignment.extend_clean_workspace {program : Observation.Program} {segment : Segment program}
    {bytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {dependencies connected reserved previous entry earlier}
    (bound : BoundSegment segment dependencies target connected reserved previous entry)
    (sameDependencies : segment.dependencies = dependencies) {scratch : Nat}
    (clean : bound.placed.freshScratch = some scratch)
    (aligned : PrefixAlignment dependencies program target.circuit entry earlier) :
    ∃ events, PrefixAlignment dependencies program target.circuit
      ⟨bound.after,entry.locations,entry.rawIndex+segment.length,entry.gateIndex+segment.count,entry.synthesis⟩
      (earlier ++ events) := by
  obtain ⟨original,trace,traceRead,traceAfter,_⟩ := bound.original_workspace_trace
  have fresh : segment.event.fresh = true := by simpa [clean] using bound.placed.scratchMode.symm
  obtain ⟨work,left,readPacket⟩ := segment.literal.emittedRead
  rw [fresh] at readPacket
  obtain ⟨wire,logical,_,_,packet⟩ := QleisliKernel.Target.CanonicalOpenQasmPlacement.clean_packet_source readPacket
  let port := segment.literal.input.port
  let operation : QleisliKernel.Semantics.Raw.Op := .certifiedCompute port.token segment.literal.emitted.dataOut
    [wire] (List.replicate (2^segment.original.layout.bits) 0) segment.literal.emitted.steps logical
  have rawOperations : segment.literal.operations = [operation] := by
    apply List.map_injective_iff.mpr (fun _ _ equal => Observation.Op.pure.inj equal)
    exact segment.literal.originalOperations.symm.trans packet
  have ports := clean_workspace_ports segment fresh
  have lookup := bound.selected
  change PureInterval.portsOf entry.raw.live
    ((segment.map.selected.map (·.port)).map (·.token)) = some (segment.map.selected.map (·.port)) at lookup
  rw [ports] at lookup
  have readPort : entry.raw.live.find? (fun candidate => candidate.token == port.token) = some port := by
    cases found : entry.raw.live.find? (fun candidate => candidate.token == port.token) with
    | none => simp [port,PureInterval.portsOf,found] at lookup
    | some selected => simpa [port,PureInterval.portsOf,found] using lookup
  have takeInput : RawTrace.take entry.raw port.token = some (port,withoutPort entry.raw port.token) := by
    simp only [RawTrace.take,readPort,bind,Option.bind]
    rfl
  let axes := RawTrace.axes entry.raw port.wires
  let expected : Event := .computed entry.raw.frame.length axes port.bits 1
    (List.replicate (2^segment.original.layout.bits) 0) segment.literal.emitted.steps logical
  have readCompute : RawTrace.step entry.raw operation = some
      (RawTrace.insert (withoutPort entry.raw port.token) segment.literal.emitted.dataOut port.wires,[expected]) := by
    simp only [operation,RawTrace.step,takeInput,bind,Option.bind]
    rfl
  have readExact := traceRead
  rw [rawOperations] at readExact
  simp only [RawTrace.interval,List.foldlM_cons,List.foldlM_nil,RawTrace.advance,readCompute,
    bind,Option.bind,pure,List.nil_append] at readExact
  have events := (congrArg RawTrace.Prepared.events (Option.some.inj readExact)).symm
  have source := Qleisli.RuntimeAdjacentSlices.readOps_pure 64 _ _ _ traceRead
  rw [← original,traceAfter] at source
  refine ⟨trace.events,.extend (rawCount := segment.length) (gateCount := segment.count) aligned rfl rfl source ?_⟩
  intro amplitude
  change RawAction.circuit [] (((target.circuit.gates.drop entry.gateIndex).take segment.count).map Instruction.step)
      (physicalColumn entry.locations amplitude) = physicalColumn entry.locations (RawAction.events dependencies trace.events amplitude)
  have targetColumn := clean_workspace_frame bound.placed clean amplitude
  dsimp only at targetColumn
  rw [← sameDependencies,events]
  have selectedAxes : (segment.map.selected.flatMap (·.port.wires)).map entry.raw.frame.idxOf = axes := by
    rw [← List.flatMap_map Binding.port]
    simp [ports,axes,RawTrace.axes,port]
  rw [selectedAxes] at targetColumn
  rw [targetColumn]
  congr 1
  obtain ⟨_,_,placed⟩ := placed_workspace_axes bound.placed.boundOwners
  rw [selectedAxes] at placed
  have actualWidth := bound.placed.body.shape
  simp only [clean,Option.toList_some,List.length_append,List.length_singleton,placed,mappedAxes,List.length_map]
    at actualWidth
  simp only [RawAction.events,List.foldl_cons,List.foldl_nil,expected]
  exact (clean_workspace_raw_event segment.literal fresh entry.raw.frame.length port.bits axes
    (Nat.add_right_cancel actualWidth) logical amplitude).symm

#print axioms PrefixAlignment.extend_clean_workspace

/-- Attach one already matched Raw operation to the checked prefix at exactly
its original cursor. The decoded interval must enact the supplied exact action. -/
theorem PrefixAlignment.extend_raw_step {dependencies program circuit entry exit earlier later}
    (aligned : PrefixAlignment dependencies program circuit entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {gateCount : Nat}
    (source : program.operations.toArray[entry.rawIndex]? = some (.pure operation))
    (step : RawTrace.step entry.raw operation = some (exit.raw,later))
    (rawEnd : exit.rawIndex = entry.rawIndex+1)
    (targetEnd : exit.gateIndex = entry.gateIndex+gateCount)
    (stepSound : ∀ amplitude,
      RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take gateCount).map Instruction.step)
        (physicalColumn entry.locations amplitude) =
      physicalColumn exit.locations (RawAction.events dependencies later amplitude)) :
    PrefixAlignment dependencies program circuit exit (earlier ++ later) := by
  have sourceList : program.operations[entry.rawIndex]? = some (.pure operation) := by
    simpa using source
  obtain ⟨inside,actual⟩ := List.getElem?_eq_some_iff.mp sourceList
  refine .extend aligned rawEnd targetEnd ?_ stepSound
  rw [List.take_one_drop_eq_of_lt_length inside,List.get_eq_getElem,actual]
  rw [QleisliKernel.Raw.ObservationAgreement.read_succ]
  simp [QleisliKernel.Raw.ObservationAgreement.layer,QleisliKernel.Raw.ObservationAgreement.readStep,
    step,bind,Option.bind,pure]

/-- Apply the exact accepted structural basis action in the current prefix.
The target word is empty and the placement itself accounts for the reordering. -/
theorem PrefixAlignment.extend_basis {dependencies program circuit connected reserved initial final prior suffix earlier}
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final prior .original suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {inputAxes outputAxes table : List Nat}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[.liftBasis bits bits inputAxes outputAxes table]))
    (unique : occurrence.entry.locations.Nodup) :
    PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ [.liftBasis bits bits inputAxes outputAxes table]) := by
  obtain ⟨_,exactExit,_⟩ := occurrence.basis_layout source read
  refine aligned.extend_raw_step (gateCount := 0) source ?_ ?_ ?_ ?_
  · have rawExit : occurrence.exit.raw = next := congrArg (fun s : State => s.raw) exactExit
    rwa [rawExit]
  · exact congrArg (fun s : State => s.rawIndex) exactExit
  · simpa only [Nat.add_zero] using congrArg (fun s : State => s.gateIndex) exactExit
  · intro amplitude
    simpa only [List.take_zero,List.map_nil,RawAction.circuit,List.foldl_nil,RawAction.events,List.foldl_cons]
      using (replayed_same_width_basis occurrence source read unique amplitude).2.symm

#print axioms PrefixAlignment.extend_raw_step
#print axioms PrefixAlignment.extend_basis

/-- A zero allocation, including the literal high-zero basis lift, consumes
one original operation while using one already reset physical coordinate. -/
theorem PrefixAlignment.extend_zero {dependencies program circuit connected reserved initial final prior suffix earlier}
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final prior .original suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {event : Event}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[event]))
    (zero : event = .init0 occurrence.entry.locations.length ∨ event = .liftBasis
      occurrence.entry.locations.length (occurrence.entry.locations.length+1) [] [occurrence.entry.locations.length] [0]) :
    PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ [event]) := by
  obtain ⟨_,_,_,_,exit,_,_⟩ := occurrence.zero_allocation source read zero
  refine aligned.extend_raw_step (gateCount := 0) source ?_ ?_ ?_ ?_
  · rw [congrArg (fun s : State => s.raw) exit]
    exact read
  · exact congrArg (fun s : State => s.rawIndex) exit
  · simpa only [Nat.add_zero] using congrArg (fun s : State => s.gateIndex) exit
  · intro amplitude
    simpa only [List.take_zero,List.map_nil,RawAction.circuit,List.foldl_nil,RawAction.events,List.foldl_cons]
      using (zero_preserves_frame occurrence source read zero amplitude).2.symm

/-- A literal owner-only transition leaves the physical coefficient column
unchanged. It still consumes its original operation and updates Raw owners. -/
theorem PrefixAlignment.extend_structural {dependencies program circuit connected reserved initial final prior suffix earlier}
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final prior .original suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[])) :
    PrefixAlignment dependencies program circuit occurrence.exit earlier := by
  obtain ⟨exit,_⟩ := occurrence.structural_empty source read
  have extended := aligned.extend_raw_step (exit := occurrence.exit) (gateCount := 0) (later := []) source
  simpa only [List.append_nil] using extended
    (by rw [congrArg (fun s : State => s.raw) exit]; exact read)
    (congrArg (fun s : State => s.rawIndex) exit)
    (by simpa only [Nat.add_zero] using congrArg (fun s : State => s.gateIndex) exit)
    (by intro amplitude; simp [exit,RawAction.circuit,RawAction.events])

/-- A literal matched circuit extends the exact original prefix with the
actual decoded gate word selected at its gate cursor. -/
theorem PrefixAlignment.extend_literal_circuit {dependencies program circuit connected reserved initial final prior suffix earlier}
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final prior .original suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Step}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps]))
    (unique : occurrence.entry.locations.Nodup) :
    PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ [.circuit bits steps]) := by
  obtain ⟨_,_,exit,_,_⟩ := occurrence.literal_circuit source read
  refine aligned.extend_raw_step (gateCount := steps.length) source ?_ ?_ ?_ ?_
  · rw [congrArg (fun s : State => s.raw) exit]
    exact read
  · exact congrArg (fun s : State => s.rawIndex) exit
  · exact congrArg (fun s : State => s.gateIndex) exit
  · intro amplitude
    simpa only [RawAction.events,List.foldl_cons,List.foldl_nil] using
      (literal_circuit_preserves_frame occurrence source read unique amplitude).2

#print axioms PrefixAlignment.extend_zero
#print axioms PrefixAlignment.extend_structural
#print axioms PrefixAlignment.extend_literal_circuit

private theorem read_single_pure {entry exit : Interface}
    {operation : QleisliKernel.Semantics.Raw.Op} {events : List Event} (fuel : Nat)
    (step : RawTrace.step entry operation = some (exit,events)) :
    Observation.readOps (fuel+1) entry [.pure operation] = some (exit,events.map Observation.Event.pure) := by
  rw [QleisliKernel.Raw.ObservationAgreement.read_succ]
  simp [QleisliKernel.Raw.ObservationAgreement.layer,QleisliKernel.Raw.ObservationAgreement.readStep,
    step,bind,Option.bind,pure]

/-- Read the exact original operations of a checked consecutive optimized
interval with the independent Raw observation reader. -/
theorem CircuitSpan.read_original {operations : List Observation.Op} {start first count : Nat}
    {frame : List Nat} {entry exit : Interface} {events : List Event} {chunks : List (List Step)}
    (trace : CircuitSpan operations.toArray start frame (List.range' first count) entry exit events chunks)
    (fuel : Nat) :
    Observation.readOps (fuel+1) entry ((operations.drop (start+first)).take count) =
      some (exit,events.map Observation.Event.pure) := by
  induction count generalizing first entry events chunks with
  | zero =>
    cases trace
    rfl
  | succ count ih =>
    change CircuitSpan operations.toArray start frame (first :: List.range' (first+1) count) entry exit events chunks at trace
    cases trace with
    | cons source step _ _ rest =>
      have read := ih rest
      rw [List.getElem?_toArray] at source
      obtain ⟨inside,op⟩ := List.getElem?_eq_some_iff.mp source
      rw [show count+1 = 1+count by omega, prefixSplit, List.take_one_drop_eq_of_lt_length inside,List.get_eq_getElem,op]
      rw [List.drop_drop,show start+first+1 = start+(first+1) by omega]
      rw [Qleisli.RuntimeAdjacentSlices.readOps_append,read_single_pure fuel step]
      simp [read,List.map_append,bind,Option.bind,pure]

#print axioms CircuitSpan.read_original

/-- Transport a clean local coefficient law through the complete declared
physical register. The same law handles structural and protected words with
any number of designated auxiliary coordinates and correlated spectators. -/
theorem clean_mapped_word (dependencies : List Dependency) (layout axes scratch : List Nat)
    (layoutUnique : layout.Nodup) (unique : (mappedAxes layout axes ++ scratch).Nodup)
    (bounds : ∀ axis ∈ axes, axis < layout.length) (separate : ∀ axis ∈ scratch, axis ∉ layout)
    (operations : List Step)
    (controls : ∀ operation ∈ operations, ∀ control ∈ operation.controls,
      control.index < axes.length+scratch.length)
    (targets : ∀ operation ∈ operations, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
      axis < axes.length+scratch.length)
    (localAction : (Nat → ℂ) → Nat → ℂ)
    (clean : ∀ (data : Nat → ℂ) row, row < 2^(axes.length+scratch.length) →
      Semantics.RawAction.circuit dependencies operations
        (Semantics.RawAction.event [] (.init0 axes.length) data) row =
      Semantics.RawAction.event [] (.init0 axes.length) (localAction data) row)
    (amplitudes : Nat → ℂ) :
    Semantics.RawAction.circuit dependencies (operations.map
      (QleisliKernel.Semantics.RawTrace.localize (mappedAxes layout axes ++ scratch)))
      (physicalColumn layout amplitudes) =
    physicalColumn layout (Semantics.RawAction.embed axes localAction amplitudes) := by
  classical
  funext row
  let selected := mappedAxes layout axes
  let coordinate := gather row (selected ++ scratch)
  let data := Semantics.RawAction.Locality.pull (gather row layout) axes amplitudes
  have width : selected.length = axes.length := List.length_map _
  have complete : (selected ++ scratch).length = axes.length+scratch.length := by
    rw [List.length_append,width]
  have inside : coordinate < 2^(axes.length+scratch.length) := by
    simpa only [coordinate,complete] using gather_bound row (selected ++ scratch)
  have low : gather row selected < 2^axes.length := by
    simpa only [width] using gather_bound row selected
  have packed : coordinate = gather row selected+2^axes.length*gather row scratch := by
    dsimp only [coordinate]
    rw [gather_append,width]
  have reset : coordinate < 2^axes.length ↔ gather row scratch = 0 := by
    constructor
    · intro h
      by_contra dirty
      have high := Nat.le_mul_of_pos_right (2^axes.length) (Nat.pos_of_ne_zero dirty)
      omega
    · intro h
      simpa only [packed,h,Nat.mul_zero,Nat.add_zero] using low
  have logicalRow : gather row selected = gather (gather row layout) axes := by
    have aligned := gather_mapped row (gather row layout) layout layoutUnique axes bounds
    rw [scatter_gather row layout layoutUnique] at aligned
    exact aligned
  rw [Semantics.RawAction.Locality.circuit_output dependencies row (selected ++ scratch) unique operations
    (by simpa only [complete] using controls) (by simpa only [complete] using targets)]
  have fibre (input : Nat) (inRange : input < 2^(axes.length+scratch.length)) :
      Semantics.RawAction.Locality.pull row (selected ++ scratch) (physicalColumn layout amplitudes) input =
        if OutsideZero (layout ++ scratch) row then
          Semantics.RawAction.event [] (.init0 axes.length) data input else 0 :=
    scratch_fibre layout axes scratch layoutUnique unique bounds separate amplitudes row input inRange
  let bounded := Qleisli.RawFiniteRows.BoundedEvent.circuit (axes.length+scratch.length) operations targets
  by_cases outside : OutsideZero (layout ++ scratch) row
  · have eqOn : Qleisli.RawFiniteRows.OnRows (axes.length+scratch.length)
        (Semantics.RawAction.Locality.pull row (selected ++ scratch) (physicalColumn layout amplitudes))
        (Semantics.RawAction.event [] (.init0 axes.length) data) := by
      intro input inRange
      exact (fibre input inRange).trans (if_pos outside)
    have same := bounded.congr dependencies _ _ eqOn coordinate inside
    simp only [Semantics.RawAction.event] at same
    rw [same]
    have localRestored := clean data coordinate inside
    simp only [Semantics.RawAction.event] at localRestored
    rw [localRestored]
    have supported : OutsideZero layout row ↔ coordinate < 2^axes.length :=
      (outside_split separate row).trans ⟨fun h => reset.mpr h.2,fun h => ⟨outside,reset.mp h⟩⟩
    by_cases lowRow : coordinate < 2^axes.length
    · have chosen : coordinate = gather (gather row layout) axes := by
        rw [packed,reset.mp lowRow,Nat.mul_zero,Nat.add_zero,logicalRow]
      simp only [physicalColumn,supported,lowRow,if_true,Semantics.RawAction.embed]
      rw [chosen]
      rfl
    · simp [physicalColumn,supported,lowRow]
  · have eqOn : Qleisli.RawFiniteRows.OnRows (axes.length+scratch.length)
        (Semantics.RawAction.Locality.pull row (selected ++ scratch) (physicalColumn layout amplitudes)) (fun _ => 0) := by
      intro input inRange
      exact (fibre input inRange).trans (if_neg outside)
    have same := bounded.congr dependencies _ _ eqOn coordinate inside
    simp only [Semantics.RawAction.event] at same
    have notSupported : ¬OutsideZero layout row := fun found => outside ((outside_split separate row).mp found).1
    rw [same,physicalColumn,if_neg notSupported]
    simpa only [mul_zero] using
      Semantics.RawAction.circuit_scale dependencies operations amplitudes 0 coordinate

#print axioms clean_mapped_word

/-- Read the input width from the original Raw transition, including the
zero preparation emitted by a basis lift. Placement does not supply it. -/
private theorem preparation_input_width {entry next : Interface}
    {operation : QleisliKernel.Semantics.Raw.Op} {event : Event}
    (read : RawTrace.step entry operation = some (next,[event])) :
    match event with
    | .init0 before | .liftBasis before _ _ _ _ => before = entry.frame.length
    | _ => True := by
  cases operation <;> simp only [RawTrace.step] at read
  all_goals repeat first
    | (have same := (Prod.mk.inj (Option.some.inj read)).2
       obtain ⟨rfl,_⟩ := List.cons.inj same
       first | rfl | exact True.intro)
    | (obtain ⟨⟨_,_⟩,_,read⟩ := Option.bind_eq_some_iff.mp read
       dsimp only at read)
    | split at read
    | cases read

/-- High-zero preparation uses the verified entry frame width in both the
Raw and physical views at the actual replay occurrence. -/
theorem PrefixAlignment.extend_preparation {dependencies program circuit connected reserved initial final prior suffix earlier}
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final prior .original suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {event : Event}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[event]))
    (width : occurrence.entry.raw.frame.length = occurrence.entry.locations.length)
    (zero : ∃ n, event = .init0 n ∨ event = .liftBasis n (n+1) [] [n] [0]) :
    PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ [event]) := by
  have geometry := preparation_input_width read
  apply PrefixAlignment.extend_zero occurrence aligned source read
  obtain ⟨bits,rfl | rfl⟩ := zero
  · exact .inl (congrArg Event.init0 (geometry.trans width))
  · exact .inr (congrArg (fun n => Event.liftBasis n (n+1) [] [n] [0]) (geometry.trans width))

#print axioms PrefixAlignment.extend_preparation

/-- Extend the actual prefix by a single checker-compared original unitary
word and its decoded decomposition. -/
theorem PrefixAlignment.extend_decomposed_circuit {dependencies program connected reserved initial final prior suffix earlier count}
    {bytes : ByteArray} {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : decode bytes = some circuit)
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final
      prior (.decomposed count) suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Step}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps]))
    (unique : occurrence.entry.locations.Nodup) :
    PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ [.circuit bits steps]) := by
  obtain ⟨_,actual,_⟩ := occurrence.decomposed_circuit source read
  refine aligned.extend_raw_step (gateCount := count) source ?_ ?_ ?_ ?_
  · rw [congrArg (fun s : State => s.raw) actual]
    exact read
  · exact congrArg (fun s : State => s.rawIndex) actual
  · exact congrArg (fun s : State => s.gateIndex) actual
  · intro amplitude
    simpa only [RawAction.events,List.foldl_cons,List.foldl_nil] using
      (decomposed_circuit_preserves_frame decoded occurrence source read unique amplitude).2

/-- Extend the actual prefix by a synthesized original word. The checked
embedding proves its scratch returns to zero in the complete physical frame. -/
theorem PrefixAlignment.extend_synthesized_circuit {dependencies program connected reserved initial final prior suffix earlier count scratch}
    {bytes : ByteArray} {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : decode bytes = some circuit)
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final
      prior (.synthesized count scratch) suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Step}
    (source : program.operations.toArray[occurrence.entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps])) :
    PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ [.circuit bits steps]) := by
  obtain ⟨_,actual,_⟩ := occurrence.synthesized_circuit source read
  refine aligned.extend_raw_step (gateCount := count) source ?_ ?_ ?_ ?_
  · rw [congrArg (fun s : State => s.raw) actual]
    exact read
  · exact congrArg (fun s : State => s.rawIndex) actual
  · exact congrArg (fun s : State => s.gateIndex) actual
  · intro amplitude
    simpa only [RawAction.events,List.foldl_cons,List.foldl_nil] using
      (synthesized_circuit_preserves_frame decoded occurrence source read amplitude).2

#print axioms PrefixAlignment.extend_decomposed_circuit
#print axioms PrefixAlignment.extend_synthesized_circuit

/-- Extend an original prefix by exactly the circuit events read across a
successfully optimized span. The original trace retains the owner-only
transitions and exact Raw and literal-gate cursor advances. -/
theorem PrefixAlignment.extend_optimized {dependencies program connected reserved initial final prior suffix earlier
    rawCount gateCount scratch bytes}
    {circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit}
    (decoded : QleisliKernel.Target.CanonicalOpenQasmResources.decode bytes = some circuit)
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved
      initial final prior (.optimized rawCount gateCount scratch) suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    (unique : occurrence.entry.locations.Nodup) :
    ∃ later, PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ later) := by
  cases scratch with
  | nil =>
    obtain ⟨next,steps,read,⟨checked⟩,exit⟩ := occurrence.optimized_decomposition
    obtain ⟨events,chunks,span,flattened⟩ := readSpan_trace read
    rw [List.range_eq_range'] at span
    refine ⟨events,.extend (rawCount := rawCount) (gateCount := gateCount) aligned
      (congrArg (fun state : State => state.rawIndex) exit)
      (congrArg (fun state : State => state.gateIndex) exit) ?_ ?_⟩
    · rw [congrArg (fun state : State => state.raw) exit]
      simpa only [Nat.add_zero] using CircuitSpan.read_original span 64
    · intro amplitude
      rw [congrArg (fun state : State => state.locations) exit,span_action span dependencies amplitude,← flattened]
      exact decomposed_preserves_frame decoded checked unique amplitude
  | cons auxiliary scratch =>
    obtain ⟨next,steps,read,⟨checked⟩,exit⟩ := occurrence.optimized_synthesis rfl
    obtain ⟨events,chunks,span,flattened⟩ := readSpan_trace read
    rw [List.range_eq_range'] at span
    refine ⟨events,.extend (rawCount := rawCount) (gateCount := gateCount) aligned
      (congrArg (fun state : State => state.rawIndex) exit)
      (congrArg (fun state : State => state.gateIndex) exit) ?_ ?_⟩
    · rw [congrArg (fun state : State => state.raw) exit]
      simpa only [Nat.add_zero] using CircuitSpan.read_original span 64
    · intro amplitude
      rw [congrArg (fun state : State => state.locations) exit,span_action span dependencies amplitude,← flattened]
      exact synthesis_preserves_frame decoded checked amplitude

#print axioms PrefixAlignment.extend_optimized

open QleisliKernel.Target.CanonicalOpenQasmPlacement (Match RawReplayKind StructuralPlacement ProtectedTablePlacement)

/-- The remaining structural action law identifies the original Raw event
with the exact target slice retained by its successful placement comparison. -/
def StructuralReplayCorrespondence (dependencies : List Dependency) (program : Observation.Program)
    (circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit) (reserved : List Nat) : Prop :=
  ∀ {entry : State} {earlier : List Event} {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface}
    {count auxiliary bits : Nat} {scratch axes : List Nat} {forward inverse : List Step}
    {uses : List QleisliKernel.Semantics.Raw.Use},
    PrefixAlignment dependencies program circuit entry earlier →
    entry.raw.frame.length = entry.locations.length → circuit.declares entry.locations →
    program.operations.toArray[entry.rawIndex]? = some (.pure operation) →
    RawTrace.step entry.raw operation = some (next,[.structuralComputed bits axes forward inverse uses]) →
    StructuralPlacement dependencies circuit entry count auxiliary scratch reserved bits axes forward inverse uses →
    (∀ step ∈ forward ++ uses.map (QleisliKernel.Raw.physicalUse 0 axes.length) ++ inverse,
      (∀ control ∈ step.controls, control.index < axes.length+1) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets step.action, axis < axes.length+1)) →
    ∀ amplitude,
      RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take count).map Instruction.step)
        (physicalColumn entry.locations amplitude) =
      physicalColumn entry.locations (RawAction.event dependencies (.structuralComputed bits axes forward inverse uses) amplitude)

/-- The remaining protected table action law uses the actual original event
and its compared target slice, including the checked workspace. -/
def ProtectedReplayCorrespondence (dependencies : List Dependency) (program : Observation.Program)
    (circuit : QleisliKernel.Target.CanonicalOpenQasmResources.Circuit) : Prop :=
  ∀ {entry : State} {earlier : List Event} {operation : QleisliKernel.Semantics.Raw.Op} {next : Interface}
    {count bits sourceBits auxiliaryBits : Nat} {workspace axes table : List Nat}
    {uses : List QleisliKernel.Semantics.Raw.Use},
    PrefixAlignment dependencies program circuit entry earlier →
    entry.raw.frame.length = entry.locations.length → circuit.declares entry.locations →
    program.operations.toArray[entry.rawIndex]? = some (.pure operation) →
    RawTrace.step entry.raw operation = some (next,[.protectedComputed bits axes sourceBits auxiliaryBits table uses]) →
    ProtectedTablePlacement dependencies circuit entry count workspace bits axes sourceBits auxiliaryBits table uses →
    bits = entry.locations.length → auxiliaryBits ≤ workspace.length → (∀ axis ∈ axes, axis < bits) →
    (∀ step ∈ ([QleisliKernel.Raw.computeStep sourceBits axes.length auxiliaryBits table] ++
      uses.map (QleisliKernel.Raw.physicalUse sourceBits axes.length) ++ [QleisliKernel.Raw.computeStep sourceBits axes.length auxiliaryBits table]),
      (∀ control ∈ step.controls, control.index < axes.length+auxiliaryBits) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets step.action, axis < axes.length+auxiliaryBits)) →
    ∀ amplitude,
      RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take count).map Instruction.step)
        (physicalColumn entry.locations amplitude) =
      physicalColumn entry.locations
        (RawAction.event dependencies (.protectedComputed bits axes sourceBits auxiliaryBits table uses) amplitude)

private theorem PrefixAlignment.extend_computed_step {dependencies program circuit entry exit earlier}
    (aligned : PrefixAlignment dependencies program circuit entry earlier)
    {operation : QleisliKernel.Semantics.Raw.Op} {event : Event} {next : Interface} {gateCount : Nat}
    (source : program.operations.toArray[entry.rawIndex]? = some (.pure operation))
    (read : RawTrace.step entry.raw operation = some (next,[event]))
    (advance : exit = {entry with raw := next, rawIndex := entry.rawIndex+1, gateIndex := entry.gateIndex+gateCount})
    (sound : ∀ amplitude,
      RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take gateCount).map Instruction.step)
        (physicalColumn entry.locations amplitude) =
      physicalColumn entry.locations (RawAction.event dependencies event amplitude)) :
    PrefixAlignment dependencies program circuit exit (earlier ++ [event]) := by
  refine aligned.extend_raw_step (gateCount := gateCount) source ?_ ?_ ?_ ?_
  · rw [congrArg (fun state : State => state.raw) advance]
    exact read
  · exact congrArg (fun state : State => state.rawIndex) advance
  · exact congrArg (fun state : State => state.gateIndex) advance
  · intro amplitude
    rw [congrArg (fun state : State => state.locations) advance]
    simpa only [RawAction.events,List.foldl_cons,List.foldl_nil] using sound amplitude

/-- Dispatch each successful replay action using its original Raw event or
optimized source span and the concrete gate slice read from the target. -/
theorem PrefixAlignment.extend_replay {dependencies program circuit connected reserved initial final prior action suffix earlier bytes}
    (decoded : QleisliKernel.Target.CanonicalOpenQasmResources.decode bytes = some circuit)
    (occurrence : ReplayOccurrence dependencies program.operations.toArray circuit connected reserved initial final prior action suffix)
    (aligned : PrefixAlignment dependencies program circuit occurrence.entry earlier)
    (width : occurrence.entry.raw.frame.length = occurrence.entry.locations.length)
    (declared : circuit.declares occurrence.entry.locations)
    (structuralSound : StructuralReplayCorrespondence dependencies program circuit reserved)
    (protectedSound : ProtectedReplayCorrespondence dependencies program circuit) :
    ∃ later, PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ later) := by
  have kind : action = .route ∨ (∃ rawCount gateCount scratch, action = .optimized rawCount gateCount scratch) ∨
      (action = .original ∨ (∃ count, action = .decomposed count) ∨
        (∃ count scratch, action = .synthesized count scratch)) := by
    cases action with
    | route => exact .inl rfl
    | optimized rawCount gateCount scratch => exact .inr (.inl ⟨rawCount,gateCount,scratch,rfl⟩)
    | original => exact .inr (.inr (.inl rfl))
    | decomposed count => exact .inr (.inr (.inr (.inl ⟨count,rfl⟩)))
    | synthesized count scratch => exact .inr (.inr (.inr (.inr ⟨count,scratch,rfl⟩)))
  rcases kind with rfl | ⟨rawCount,gateCount,scratch,rfl⟩ | single
  · exact ⟨[],by simpa only [List.append_nil] using aligned.extend_route occurrence⟩
  · exact PrefixAlignment.extend_optimized decoded occurrence aligned declared.1
  · obtain ⟨operation,next,events,source,read,rawKind⟩ := occurrence.raw_event single
    cases rawKind with
    | structural =>
      exact ⟨[],by simpa only [List.append_nil] using PrefixAlignment.extend_structural occurrence aligned source read⟩
    | init0 bits =>
      exact ⟨_,PrefixAlignment.extend_preparation occurrence aligned source read width ⟨bits,.inl rfl⟩⟩
    | prepZero bits =>
      exact ⟨_,PrefixAlignment.extend_preparation occurrence aligned source read width ⟨bits,.inr rfl⟩⟩
    | basis bits inputAxes outputAxes table =>
      exact ⟨_,PrefixAlignment.extend_basis occurrence aligned source read declared.1⟩
    | literal bits steps =>
      exact ⟨_,PrefixAlignment.extend_literal_circuit occurrence aligned source read declared.1⟩
    | decomposition count bits steps =>
      exact ⟨_,PrefixAlignment.extend_decomposed_circuit decoded occurrence aligned source read declared.1⟩
    | synthesis count bits scratch steps =>
      exact ⟨_,PrefixAlignment.extend_synthesized_circuit decoded occurrence aligned source read⟩
    | structuralCompute count bits auxiliary scratch axes forward inverse uses =>
      obtain ⟨⟨placed⟩,exit⟩ := occurrence.structural_computed source read
      exact ⟨_,aligned.extend_computed_step source read exit
        (structuralSound aligned width declared source read placed (occurrence.structural_geometry source read))⟩
    | protectedDecomposition count bits sourceBits axes table uses =>
      obtain ⟨⟨placed⟩,exit,_⟩ := occurrence.protected_table
        (count := count) (workspace := []) source read (.inr ⟨rfl,rfl,rfl⟩)
      obtain ⟨liveWidth,auxBound,axesBounds,wordBounds⟩ := occurrence.protected_geometry
        (count := count) (workspace := []) source read (.inr ⟨rfl,rfl,rfl⟩)
      exact ⟨_,aligned.extend_computed_step source read exit
        (protectedSound aligned width declared source read placed liveWidth auxBound axesBounds wordBounds)⟩
    | protectedSynthesis count bits sourceBits auxiliaryBits workspace axes table uses =>
      obtain ⟨⟨placed⟩,exit,_⟩ := occurrence.protected_table
        (count := count) (workspace := workspace) source read (.inl rfl)
      obtain ⟨liveWidth,auxBound,axesBounds,wordBounds⟩ := occurrence.protected_geometry
        (count := count) (workspace := workspace) source read (.inl rfl)
      exact ⟨_,aligned.extend_computed_step source read exit
        (protectedSound aligned width declared source read placed liveWidth auxBound axesBounds wordBounds)⟩

#print axioms PrefixAlignment.extend_replay

open QleisliKernel.Target.CanonicalOpenQasmPlacement (ReplaySteps Segment BoundSegment WorkspaceTrace FinishedTrace)

/-- Iterate the local semantic cases over the ordered, actual placement replay. -/
theorem ReplaySteps.extend_prefix {bytes dependencies program circuit connected reserved steps entry exit prior}
    (decoded : QleisliKernel.Target.CanonicalOpenQasmResources.decode bytes = some circuit)
    (replay : ReplaySteps dependencies program.operations.toArray circuit connected reserved steps entry exit)
    (aligned : PrefixAlignment dependencies program circuit entry prior)
    (width : entry.raw.frame.length = entry.locations.length)
    (declared : circuit.declares entry.locations)
    (localSound : ∀ {before after action} (occurrence : ReplayOccurrence dependencies program.operations.toArray
        circuit connected reserved before after [] action []) {earlier},
      PrefixAlignment dependencies program circuit occurrence.entry earlier →
      occurrence.entry.raw.frame.length = occurrence.entry.locations.length → circuit.declares occurrence.entry.locations →
      ∃ later, PrefixAlignment dependencies program circuit occurrence.exit (earlier ++ later)) :
    ∃ events, PrefixAlignment dependencies program circuit exit events := by
  induction replay generalizing prior with
  | empty _ => exact ⟨prior,aligned⟩
  | next occurrence atEntry atExit tail ih =>
    have localWidth : occurrence.entry.raw.frame.length = occurrence.entry.locations.length := atEntry.symm ▸ width
    have localDeclared : circuit.declares occurrence.entry.locations := atEntry.symm ▸ declared
    obtain ⟨later,sound⟩ := localSound occurrence (atEntry.symm ▸ aligned) localWidth localDeclared
    obtain ⟨exitWidth,exitDeclared⟩ := occurrence.exit_geometry decoded localWidth localDeclared
    exact ih (atExit ▸ sound) (atExit ▸ exitWidth) (atExit ▸ exitDeclared)

/-- Compose the local replay cases, original workspace steps and final suffix
from the initial empty Raw frame to the actual checked readout cursor. -/
theorem FinishedTrace.align_prefix {bytes capacity}
    {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {dependencies program connected reserved synthesis suffix}
    (finished : FinishedTrace program dependencies target connected reserved synthesis suffix)
    {segments : List (Segment program)}
    (visited : finished.recorded.trace.RecordsSegments segments)
    (sameDependencies : ∀ segment ∈ segments, segment.dependencies = dependencies)
    (localSound : ∀ {before after action} (occurrence : ReplayOccurrence dependencies program.operations.toArray
        target.circuit connected reserved before after [] action []) {earlier},
      PrefixAlignment dependencies program target.circuit occurrence.entry earlier →
      occurrence.entry.raw.frame.length = occurrence.entry.locations.length → target.circuit.declares occurrence.entry.locations →
      ∃ later, PrefixAlignment dependencies program target.circuit occurrence.exit (earlier ++ later))
    (workspaceSound : ∀ {segment previous entry} (bound : BoundSegment (program := program)
        segment dependencies target connected reserved previous entry) (exit : State) {earlier},
      segment.dependencies = dependencies →
      exit.raw = bound.after → exit.locations = entry.locations → exit.synthesis = entry.synthesis →
      exit.rawIndex = entry.rawIndex+segment.length →
      exit.gateIndex = entry.gateIndex+((target.circuit.gates.drop entry.gateIndex).take segment.count).length →
      PrefixAlignment dependencies program target.circuit entry earlier →
      ∃ later, PrefixAlignment dependencies program target.circuit exit (earlier ++ later)) :
    ∃ events, PrefixAlignment dependencies program target.circuit finished.final events := by
  have workspaces {state uses peak}
      {trace : WorkspaceTrace (program := program) dependencies target connected reserved synthesis state uses peak}
      {segments : List (Segment program)} (visited : trace.RecordsSegments segments)
      (dependenciesKept : ∀ segment ∈ segments, segment.dependencies = dependencies) :
      ∃ events, PrefixAlignment dependencies program target.circuit state events := by
    induction visited with
    | start => exact ⟨[],.start synthesis⟩
    | @next _ _ segment _ _ earlierTrace previous bound _ ih =>
      obtain ⟨_,before⟩ := ih (fun earlier inPrevious => dependenciesKept earlier (List.mem_append_left _ inPrevious))
      obtain ⟨_,entry⟩ := ReplaySteps.extend_prefix target.original bound.prefix_steps before
        earlierTrace.preserves_width earlierTrace.declares_locations localSound
      obtain ⟨raw,layout,source,target⟩ := bound.exit_coordinates
      have last := dependenciesKept segment (List.mem_append_right previous List.mem_cons_self)
      obtain ⟨_,after⟩ := workspaceSound bound _ last raw layout rfl source target entry
      exact ⟨_,after⟩
  obtain ⟨_,aligned⟩ := workspaces visited sameDependencies
  exact ReplaySteps.extend_prefix target.original finished.suffix_steps aligned
    finished.recorded.trace.preserves_width finished.recorded.trace.declares_locations localSound

#print axioms FinishedTrace.align_prefix

open QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5 (Original CheckedPlacement)

/-- Compose the recorded actual workspaces using their checked original
owner slices and the same root dependency table. Local replay cases are the
only remaining premise of this accepted-placement lemma. -/
theorem aligned_checked_placement {sourceBytes : ByteArray} {original : Original sourceBytes}
    {targetBytes capacity} {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked targetBytes capacity}
    {connected reserved synthesis plans suffix}
    (checked : CheckedPlacement original target connected reserved synthesis plans suffix)
    (eachStep : ∀ {before after action} (occurrence : ReplayOccurrence original.checked.root.dependencies
        original.checked.root.program.operations.toArray target.circuit connected reserved before after [] action [])
      {earlier}, PrefixAlignment original.checked.root.dependencies original.checked.root.program
        target.circuit occurrence.entry earlier →
      occurrence.entry.raw.frame.length = occurrence.entry.locations.length → target.circuit.declares occurrence.entry.locations →
      ∃ later, PrefixAlignment original.checked.root.dependencies original.checked.root.program target.circuit
        occurrence.exit (earlier ++ later)) :
    ∃ events, PrefixAlignment original.checked.root.dependencies original.checked.root.program target.circuit
      checked.trace.final events := by
  obtain ⟨_,listed,rootDependencies⟩ := checked.workspaceDependencies
  refine FinishedTrace.align_prefix checked.trace listed rootDependencies eachStep ?_
  intro segment previous entry bound exit earlier dependencies unchangedRaw unchangedLocation unchangedSynthesis sourceCursor targetCursor aligned
  have enough := (QleisliKernel.Target.CanonicalOpenQasmWorkspace.interval_length bound.placed.body.actualInterval).2
  change entry.gateIndex+segment.count ≤ target.circuit.gates.length at enough
  have wordLength : ((target.circuit.gates.drop entry.gateIndex).take segment.count).length = segment.count := by
    simp only [List.length_take,List.length_drop]
    omega
  rw [wordLength] at targetCursor
  have exitState : exit = ⟨bound.after,entry.locations,entry.rawIndex+segment.length,
      entry.gateIndex+segment.count,entry.synthesis⟩ := by
    cases exit
    simp_all only
  rw [exitState]
  cases scratch : bound.placed.freshScratch with
  | some wire => exact PrefixAlignment.extend_clean_workspace bound dependencies scratch aligned
  | none =>
    have safe := original.root_safe.2.1
    have closed := List.isEmpty_iff.mp checked.trace.closed.1
    obtain ⟨before,after,suffixRun,initial⟩ :=
      Qleisli.RuntimeTerminalRawMarginal.ownership_after_closed_pure_prefix safe closed (aligned.read_prefix closed)
    rw [← List.take_append_drop segment.length (original.checked.root.program.operations.drop entry.rawIndex)] at suffixRun
    obtain ⟨done_,workspaceRun,_,_⟩ := Ownership.Run.split _ _ suffixRun
    exact PrefixAlignment.extend_dirty_workspace bound dependencies scratch initial workspaceRun aligned

#print axioms aligned_checked_placement

open QleisliKernel.Qirf.RuntimeInterval (Computed)

private theorem position_lookup (values : List Nat) :
    (List.range values.length).map (fun index => (values[index]?).getD 0) = values := by
  apply List.ext_getElem
  · simp
  · intro index lhs rhs
    simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem rhs,Option.getD_some]

private theorem matrix_step_targets_distinct {dependencies bits steps matrix work left}
    (accepted : (QleisliKernel.Finite.circuitMatrix dependencies
      (QleisliKernel.Raw.circuit bits steps)).run work = (.ok matrix,left))
    (step : Step) (member : step ∈ steps) : (QleisliKernel.Finite.targets step.action).Nodup := by
  have valid := (QleisliKernel.Finite.circuitMatrix_columns _ _ _ _ _ accepted).1
  have all : steps.all (QleisliKernel.Finite.stepValid dependencies bits) = true := by
    simpa only [QleisliKernel.Raw.circuit,register_width] using (Bool.and_eq_true_iff.mp valid).2
  have action := List.all_eq_true.mp all step member
  have axes := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp action).1).2
  have unique := (Bool.and_eq_true_iff.mp axes).2
  exact (List.nodup_append.mp (QleisliKernel.Raw.Ownership.unique_nodup _ unique)).2.1

private theorem protected_input_distinct {dependencies : List Dependency} {sourceBits dataBits auxiliaryBits localWidth : Nat}
    {table inner outer : List Nat} {tail : List Step} {matrix : QleisliKernel.Semantics.Exact.Matrix}
    (width : inner.length = dataBits+auxiliaryBits)
    (checked : Computed (QleisliKernel.Finite.circuitMatrix dependencies
      (QleisliKernel.Raw.circuit localWidth
        (((QleisliKernel.Raw.computeStep sourceBits dataBits auxiliaryBits table :: tail).map
          (QleisliKernel.Semantics.RawTrace.localize inner)).map (QleisliKernel.Semantics.RawTrace.localize outer)))) matrix) :
    inner.Nodup := by
  obtain ⟨work,left,ran⟩ := checked
  let compute := QleisliKernel.Raw.computeStep sourceBits dataBits auxiliaryBits table
  let step := QleisliKernel.Semantics.RawTrace.localize outer (QleisliKernel.Semantics.RawTrace.localize inner compute)
  have member : step ∈ ((compute :: tail).map (QleisliKernel.Semantics.RawTrace.localize inner)).map
      (QleisliKernel.Semantics.RawTrace.localize outer) := by simp [step]
  have unique := matrix_step_targets_distinct ran step member
  change (((List.range (dataBits+auxiliaryBits)).map (fun index => (inner[index]?).getD 0)).map
    (fun index => (outer[index]?).getD 0)).Nodup at unique
  rw [← width,position_lookup] at unique
  exact List.Nodup.of_map _ unique

private theorem localize_step_bounds {outer : List Nat} {width : Nat}
    (carrierBounds : ∀ axis ∈ outer, axis < width) (step : Step)
    (controlBound : ∀ control ∈ step.controls, control.index < outer.length)
    (targetBound : ∀ axis ∈ QleisliKernel.Finite.targets step.action, axis < outer.length) :
    (∀ control ∈ (RawTrace.localize outer step).controls, control.index < width) ∧
    (∀ axis ∈ QleisliKernel.Finite.targets (RawTrace.localize outer step).action, axis < width) := by
  have coordinate (index : Nat) (within : index < outer.length) : (outer[index]?).getD 0 < width := by
    rw [List.getElem?_eq_getElem within,Option.getD_some]
    exact carrierBounds _ (List.getElem_mem within)
  constructor
  · intro control member
    change control ∈ step.controls.map (fun op => (⟨(outer[op.index]?).getD 0,op.whenOne⟩ : Control)) at member
    obtain ⟨op,present,rfl⟩ := List.mem_map.mp member
    exact coordinate _ (controlBound _ present)
  · have targets : QleisliKernel.Finite.targets (RawTrace.localize outer step).action =
        (QleisliKernel.Finite.targets step.action).map (fun index => (outer[index]?).getD 0) := by
      obtain ⟨_,action⟩ := step
      cases action <;> rfl
    intro axis member
    rw [targets] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact coordinate _ (targetBound _ present)

private theorem auxiliary_layout {locations axes auxiliary : List Nat} {bits auxiliaryBits : Nat}
    (liveWidth : bits = locations.length) (auxiliaryWidth : auxiliary.length = auxiliaryBits)
    (axisBounds : ∀ axis ∈ axes, axis < bits) :
    mappedAxes (locations ++ auxiliary) (axes ++ (List.range auxiliaryBits).map (bits+·)) =
      mappedAxes locations axes ++ auxiliary := by
  simp only [mappedAxes,List.map_append,List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro axis member
    rw [List.getElem?_append_left (liveWidth ▸ axisBounds axis member)]
  · conv => rhs; rw [← position_lookup auxiliary,auxiliaryWidth]
    apply List.map_congr_left
    intro index _
    have after : locations.length ≤ bits+index := by omega
    change ((locations ++ auxiliary)[bits+index]?).getD 0 = (auxiliary[index]?).getD 0
    rw [List.getElem?_append_right after,← liveWidth,Nat.add_sub_cancel_left]

private theorem map_positions_unique {locations axes : List Nat} (unique : locations.Nodup)
    (ordered : axes.Nodup) (bounded : ∀ axis ∈ axes, axis < locations.length) : (mappedAxes locations axes).Nodup := by
  apply List.Nodup.map_on _ ordered
  intro first firstMember second secondMember same
  have left := bounded first firstMember
  have right := bounded second secondMember
  apply (List.getElem?_inj left unique).mp
  rw [List.getElem?_eq_getElem left,List.getElem?_eq_getElem right]
  simpa only [List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,Option.getD_some,Option.some.injEq] using same

/-- The original verifier and aligned source prefix identify the same checked
protected event. Its real gate interval has the full source action after the
original auxiliary and any synthesis scratch have each returned to zero. -/
theorem protected_replay_sound {bytes dependencies program circuit original work left}
    (decoded : decode bytes = some circuit)
    (closed : program.inputs = []) (noClassical : program.classicalInputs = [])
    (verified : (QleisliKernel.Raw.Observation.verify dependencies program).run work = (.ok original,left)) :
    ProtectedReplayCorrespondence dependencies program circuit := by
  intro entry earlier operation next count bits sourceBits auxiliaryBits workspace axes table uses
    aligned _ declared source raw placed bitsEq auxWithin axisBounds wordBounds amplitudes
  rw [List.getElem?_toArray] at source
  have sourceList := source
  obtain ⟨checkedEntry,_,_,_,owned,checked⟩ := QleisliKernel.Raw.Observation.verify_closed_step closed noClassical sourceList verified
  have prefixRead := aligned.read_prefix closed
  rw [closed] at prefixRead
  have exactEntry := Qleisli.RuntimeTerminalRawMarginal.ownership_pure_read_interface owned 64
    prefixRead (by
      intro event member
      obtain ⟨real,_,rfl⟩ := List.mem_map.mp member
      exact ⟨real,rfl⟩)
  change entry.raw = checkedEntry.quantum.reference at exactEntry
  have checkedRead := raw
  rw [exactEntry] at checkedRead
  obtain ⟨_,sourceWidth,tableCheck,useCheck⟩ := QleisliKernel.Raw.Observation.checkStep_protected_table checkedRead checked
  let auxiliary := workspace.take auxiliaryBits
  let carrier := entry.locations ++ auxiliary
  let inner := axes ++ (List.range auxiliaryBits).map (bits+·)
  let compute := QleisliKernel.Raw.computeStep sourceBits axes.length auxiliaryBits table
  let tail := uses.map (QleisliKernel.Raw.physicalUse sourceBits axes.length) ++ [compute]
  let word := compute :: tail
  let extended := word.map (RawTrace.localize inner)
  let initial := RawAction.event [] (.init0 entry.locations.length) amplitudes
  have auxWidth : auxiliary.length = auxiliaryBits := by simp [auxiliary,Nat.min_eq_left auxWithin]
  have innerWidth : inner.length = axes.length+auxiliaryBits := by simp [inner]
  have innerBounds : ∀ axis ∈ inner, axis < carrier.length := by
    intro axis member
    rcases List.mem_append.mp member with data | scratch
    · simpa only [carrier,List.length_append,auxWidth,← bitsEq] using
        Nat.lt_of_lt_of_le (axisBounds axis data) (Nat.le_add_right bits auxiliaryBits)
    · obtain ⟨offset,inside,rfl⟩ := List.mem_map.mp scratch
      simpa only [carrier,List.length_append,auxWidth,← bitsEq] using
        Nat.add_lt_add_left (List.mem_range.mp inside) bits
  have carrierUnique : carrier.Nodup := (List.nodup_append.mp placed.declared.1).1
  have embedded : physicalColumn carrier initial = physicalColumn entry.locations amplitudes :=
    extend_reset_frame entry.locations auxiliary carrierUnique amplitudes
  have compared : inner.Nodup ∧
      RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take count).map Instruction.step)
        (physicalColumn entry.locations amplitudes) =
      physicalColumn carrier (RawAction.circuit dependencies extended initial) := by
    cases empty : (workspace.drop auxiliaryBits).isEmpty with
    | true =>
      obtain ⟨wordCheck⟩ := placed.decomposed_word empty
      refine ⟨protected_input_distinct (sourceBits := sourceBits) (table := table) (tail := tail)
        (outer := (List.range carrier.length).map wordCheck.axes.idxOf) innerWidth wordCheck.originalOperator,?_⟩
      have equivalent := decomposed_preserves_frame decoded wordCheck carrierUnique initial
      change RawAction.circuit [] _ (physicalColumn carrier initial) = _ at equivalent
      rw [embedded] at equivalent
      exact equivalent
    | false =>
      obtain ⟨wordCheck⟩ := placed.synthesized_word empty
      refine ⟨protected_input_distinct (sourceBits := sourceBits) (table := table) (tail := tail)
        (outer := (List.range carrier.length).map wordCheck.axes.idxOf) innerWidth wordCheck.originalOperator,?_⟩
      have equivalent := synthesis_preserves_frame decoded wordCheck initial
      change RawAction.circuit [] _ (physicalColumn carrier initial) = _ at equivalent
      rw [embedded] at equivalent
      exact equivalent
  have exactAxes : mappedAxes carrier inner = mappedAxes entry.locations axes ++ auxiliary :=
    auxiliary_layout bitsEq auxWidth axisBounds
  have jointUnique : (mappedAxes entry.locations axes ++ auxiliary).Nodup :=
    exactAxes ▸ map_positions_unique carrierUnique compared.1 innerBounds
  have apart : ∀ wire ∈ auxiliary, wire ∉ entry.locations := by
    intro wire member inside
    exact (List.nodup_append.mp carrierUnique).2.2 wire inside wire member rfl
  have outerBounds : ∀ op ∈ extended,
      (∀ control ∈ op.controls, control.index < carrier.length) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets op.action, axis < carrier.length) := by
    intro op appears
    obtain ⟨step,held,rfl⟩ := List.mem_map.mp appears
    have original := wordBounds step held
    exact localize_step_bounds innerBounds step
      (fun c member => innerWidth.symm ▸ original.1 c member)
      (fun a member => innerWidth.symm ▸ original.2 a member)
  have localization : extended.map (RawTrace.localize carrier) =
      word.map (RawTrace.localize (mappedAxes entry.locations axes ++ auxiliary)) := by
    simp only [extended,List.map_map,← exactAxes]
    apply List.map_congr_left
    intro step member
    have original := wordBounds step member
    exact Qleisli.RuntimeTraceAxes.localize_comp carrier inner step
      (fun c held => innerWidth.symm ▸ original.1 c held)
      (fun a held => innerWidth.symm ▸ original.2 a held)
  have bounds (step : Step) (member : step ∈ word) := wordBounds step member
  have clean : ∀ (data : Nat → ℂ) row, row < 2^(axes.length+auxiliary.length) →
      RawAction.circuit dependencies word (RawAction.event [] (.init0 axes.length) data) row =
        RawAction.event [] (.init0 axes.length) (Qleisli.ProtectedComputeAction.logical sourceBits table uses data) row := by
    intro data row inside
    rw [auxWidth] at inside
    exact Qleisli.ProtectedComputeAction.literal_clean dependencies sourceWidth table tableCheck uses useCheck data row inside
  have restored := clean_mapped_word dependencies entry.locations axes auxiliary declared.1 jointUnique
    (fun a mem => bitsEq ▸ axisBounds a mem) apart word
    (fun step member c held => auxWidth.symm ▸ (bounds step member).1 c held)
    (fun step member a held => auxWidth.symm ▸ (bounds step member).2 a held)
    (Qleisli.ProtectedComputeAction.logical sourceBits table uses) clean amplitudes
  rw [compared.2,← localized_circuit_frame dependencies carrier carrierUnique extended outerBounds initial,
    embedded,localization,restored,
    Qleisli.ProtectedComputeAction.raw_event_embed dependencies axes table uses useCheck amplitudes]

#print axioms protected_replay_sound

/-- The checked structural gate interval enacts the exact original Raw
compute/use/inverse with the designated predicate line restored to zero. -/
theorem structural_replay_sound {bytes dependencies program circuit reserved original work left}
    (decoded : decode bytes = some circuit)
    (closed : program.inputs = []) (noClassical : program.classicalInputs = [])
    (verified : (QleisliKernel.Raw.Observation.verify dependencies program).run work = (.ok original,left)) :
    StructuralReplayCorrespondence dependencies program circuit reserved := by
  intro entry earlier operation next count auxiliary bits scratch axes forward inverse uses
    aligned _ declared source raw placed wordBounds amplitudes
  rw [List.getElem?_toArray] at source
  obtain ⟨checkedEntry,_,_,_,owned,checked⟩ :=
    QleisliKernel.Raw.Observation.verify_closed_step closed noClassical source verified
  have rawPrefix := aligned.read_prefix closed
  rw [closed] at rawPrefix
  have entrySame := Qleisli.RuntimeTerminalRawMarginal.ownership_pure_read_interface owned 64 rawPrefix (by
      intro event member
      obtain ⟨real,_,rfl⟩ := List.mem_map.mp member
      exact ⟨real,rfl⟩)
  change entry.raw = checkedEntry.quantum.reference at entrySame
  rw [entrySame] at raw
  obtain ⟨_,_,_,accepted⟩ := QleisliKernel.Raw.Observation.checkStep_pure_event raw checked
  simp only [QleisliKernel.Raw.Pure.eventCheck] at accepted
  obtain ⟨_,_,guarded,rest⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ accepted
  obtain ⟨clauses,_,checkedClauses,_⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ rest
  have verifiedClauses := (QleisliKernel.Finite.lift_success _ _ _ _ checkedClauses).1
  have checkedAxes := (QleisliKernel.Finite.guard_success _ _ _ _ guarded).1
  have distinct : axes.Nodup := by
    simp only [QleisliKernel.Finite.axesValid,Bool.and_eq_true] at checkedAxes
    exact QleisliKernel.Raw.Ownership.unique_nodup _ checkedAxes.2
  let carrier := entry.locations ++ [auxiliary]
  let inner := axes ++ [bits]
  let word := forward ++ uses.map (QleisliKernel.Raw.physicalUse 0 axes.length) ++ inverse
  let extended := word.map (RawTrace.localize inner)
  let initial := RawAction.event [] (.init0 entry.locations.length) amplitudes
  let logical := fun data => RawAction.circuit []
    (forward ++ uses.map (QleisliKernel.Semantics.Protected.physical 0 axes.length) ++ inverse)
    (RawAction.event [] (.init0 axes.length) data)
  have verifiedBounds : ∀ a ∈ axes, a < bits := fun a mem =>
    of_decide_eq_true (List.all_eq_true.mp placed.inFrame.2 a mem)
  have innerBounds : ∀ a ∈ inner, a < carrier.length := by
    intro a mem
    rcases List.mem_append.mp mem with data | predicate
    · have bound := verifiedBounds a data
      simp only [carrier,List.length_append,List.length_singleton,← placed.inFrame.1]
      omega
    · have same : a = bits := List.mem_singleton.mp predicate
      simp [same,carrier,placed.inFrame.1]
  have carrierUnique : carrier.Nodup := (List.nodup_append.mp placed.declared.1).1
  have innerUnique : inner.Nodup := by
    refine List.nodup_append.mpr ⟨distinct,by simp,?_⟩
    intro a inAxes other inSingleton same
    obtain rfl := List.mem_singleton.mp inSingleton
    exact (Nat.ne_of_lt (verifiedBounds a inAxes)) same
  have exactAxes : mappedAxes carrier inner = mappedAxes entry.locations axes ++ [auxiliary] := by
    exact auxiliary_layout (auxiliaryBits := 1) placed.inFrame.1 rfl verifiedBounds
  have jointUnique : (mappedAxes entry.locations axes ++ [auxiliary]).Nodup :=
    exactAxes ▸ map_positions_unique carrierUnique innerUnique innerBounds
  have separate : ∀ a ∈ [auxiliary], a ∉ entry.locations := by
    intro a present inside
    exact (List.nodup_append.mp carrierUnique).2.2 a inside a present rfl
  have embedded : physicalColumn carrier initial = physicalColumn entry.locations amplitudes :=
    extend_reset_frame entry.locations [auxiliary] carrierUnique amplitudes
  have compared : RawAction.circuit [] (((circuit.gates.drop entry.gateIndex).take count).map Instruction.step)
      (physicalColumn entry.locations amplitudes) = physicalColumn carrier (RawAction.circuit dependencies extended initial) := by
    rw [← embedded]
    cases empty : scratch.isEmpty with
    | true =>
      obtain ⟨wordCheck⟩ := placed.decomposed_word empty
      exact decomposed_preserves_frame decoded wordCheck carrierUnique initial
    | false =>
      obtain ⟨wordCheck⟩ := placed.synthesized_word empty
      exact synthesis_preserves_frame decoded wordCheck initial
  have innerWidth : inner.length = axes.length+1 := by simp [inner]
  have outerBounds : ∀ step ∈ extended,
      (∀ control ∈ step.controls, control.index < carrier.length) ∧
      (∀ a ∈ QleisliKernel.Finite.targets step.action, a < carrier.length) := by
    intro op appears
    obtain ⟨step,held,rfl⟩ := List.mem_map.mp appears
    have bounds := wordBounds step held
    exact localize_step_bounds innerBounds step
      (fun c present => innerWidth.symm ▸ bounds.1 c present)
      (fun a present => innerWidth.symm ▸ bounds.2 a present)
  have localization : extended.map (RawTrace.localize carrier) =
      word.map (RawTrace.localize (mappedAxes entry.locations axes ++ [auxiliary])) := by
    simp only [extended,List.map_map,← exactAxes]
    apply List.map_congr_left
    intro step member
    have bounds := wordBounds step member
    exact Qleisli.RuntimeTraceAxes.localize_comp carrier inner step
      (fun c present => innerWidth.symm ▸ bounds.1 c present)
      (fun a present => innerWidth.symm ▸ bounds.2 a present)
  have restored := clean_mapped_word dependencies entry.locations axes [auxiliary] declared.1 jointUnique
    (fun a mem => placed.inFrame.1 ▸ verifiedBounds a mem) separate word
    (fun step member => (wordBounds step member).1) (fun step member => (wordBounds step member).2)
    logical (Qleisli.StructuralComputedRestoration.raw_structural_clean verifiedClauses dependencies) amplitudes
  rw [compared,← localized_circuit_frame dependencies carrier carrierUnique extended outerBounds initial,
    embedded,localization,restored]
  rfl

#print axioms structural_replay_sound

open Qleisli.RuntimeObservingComposition (runHistories runHistories_append runHistories_singleton)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory run_pure)

private noncomputable def finalizeHistory (dependencies : List Dependency)
    (history : ObservingAction.History) : ObservingAction.History :=
  pureHistory dependencies [.reorder 0 []] history

private theorem finalizeHistory_coefficient (dependencies : List Dependency)
    (history : ObservingAction.History) (column : Nat) :
    (finalizeHistory dependencies history).operator 0 column = history.operator 0 column := by
  exact Qleisli.RuntimeNamedCallerAction.reorder_self dependencies [] List.nodup_nil
    (fun row => history.operator row column) 0 (by decide)

private theorem run_final_reorder (dependencies : List Dependency) (fuel : Nat)
    (histories : List ObservingAction.History) :
    runHistories dependencies (fuel+1) [.pure (.reorder 0 [])] histories =
      some (histories.map (finalizeHistory dependencies)) := by
  have singleton (history : ObservingAction.History) :
      ObservingAction.run dependencies (fuel+1) [.pure (.reorder 0 [])] history =
        some [finalizeHistory dependencies history] := by
    change ObservingAction.run dependencies (fuel+1)
      ([.reorder 0 []].map Observation.Event.pure) history = _
    exact run_pure dependencies fuel [.reorder 0 []] history
  have groups : histories.mapM (ObservingAction.run dependencies (fuel+1) [.pure (.reorder 0 [])]) =
      some (histories.map (fun history => [finalizeHistory dependencies history])) := by
    induction histories with
    | nil => rfl
    | cons first later ih =>
      simp [List.mapM_cons,singleton,ih,bind,Option.bind,pure]
  unfold runHistories
  rw [groups]
  change some (histories.map (fun history => [finalizeHistory dependencies history])).flatten = _
  congr 1
  clear groups singleton
  induction histories with
  | nil => rfl
  | cons first later ih => simp [ih]

/-- Select an original history by its ordered public result. -/
noncomputable def rawOutcomeWeight (program : Observation.Program)
    (outcome : List Bool) (writes : List (Nat × Bool)) : ℂ :=
  if program.classicalOutputs.mapM (RawInstrument.value writes) = some outcome then 1 else 0

/-- Once the actual accepted prefix alignment reaches the readout cursor,
compare the complete original Raw program with the actual decoded reset,
complete literal gate word, and terminal measurement word. Hidden outcomes
remain in the original history sum. -/
theorem FinishedTrace.exact_terminal_output {bytes capacity}
    {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Observation.Program} {dependencies connected reserved synthesis suffix events}
    (finished : QleisliKernel.Target.CanonicalOpenQasmPlacement.FinishedTrace
      program dependencies target connected reserved synthesis suffix)
    (aligned : PrefixAlignment dependencies program target.circuit finished.final events)
    {entry exit : Ownership.State}
    (ownership : Ownership.Run entry (program.operations.drop finished.final.rawIndex) exit)
    (same : entry.interface = finished.final.raw)
    (classical outcome : List Bool) :
    ∃ histories, ObservingAction.program dependencies program classical = some histories ∧
      ((histories.map fun history =>
        history.operator 0 0 * star (history.operator 0 0) * rawOutcomeWeight program outcome history.values).sum) =
      ∑ physical ∈ Finset.range (2^target.circuit.qubits),
        if target.circuit.measurements.map (fun axis => bit physical axis == 1) = outcome then
          resetPrefix target.circuit target.circuit.gates.length physical *
            star (resetPrefix target.circuit target.circuit.gates.length physical)
        else 0 := by
  classical
  have closed : program.inputs = [] := List.isEmpty_iff.mp finished.closed.1
  have noClassical : program.classicalInputs = [] := List.isEmpty_iff.mp finished.closed.2
  have layout := finished.readout_declares
  obtain ⟨prefixHistory,prefixRead,prefixRun,emptyValues,_,embedded⟩ :=
    aligned.closed_history closed noClassical classical
  obtain ⟨later,trace,suffixRead,emptyFrame,writes⟩ :=
    Qleisli.RuntimeTerminalRawMarginal.readout_original_word finished.readout layout.1 ownership same 64
  let initial := ObservingAction.initial (program.classicalInputs.zip classical)
  obtain ⟨terminal,suffixRun,marginal⟩ :=
    trace.run_weighted dependencies 64 prefixHistory 0 0 (rawOutcomeWeight program outcome)
  have wholeRead : Observation.readOps 65 (RawTrace.initial program.inputs) program.operations =
      some (exit.interface,events.map Observation.Event.pure ++ later) := by
    conv_lhs => rw [← List.take_append_drop finished.final.rawIndex program.operations]
    rw [Qleisli.RuntimeAdjacentSlices.readOps_append 64,prefixRead]
    change (do
      let result ← Observation.readOps 65 finished.final.raw (program.operations.drop finished.final.rawIndex)
      pure (result.1,events.map Observation.Event.pure ++ result.2)) = _
    rw [suffixRead]
    rfl
  have returned := finished.readout.original_trace.1
  have programRead : Observation.read program = some ⟨exit.interface,
      (events.map Observation.Event.pure ++ later) ++ [.pure (.reorder 0 [])],
      (RawTrace.initial program.inputs).frame.length⟩ := by
    unfold Observation.read
    simp [wholeRead,returned,emptyFrame,RawTrace.axes,Ownership.State.interface,bind,Option.bind,pure]
  refine ⟨terminal.map (finalizeHistory dependencies),?_,?_⟩
  · unfold ObservingAction.program
    rw [programRead]
    change ObservingAction.run dependencies 65
      ((events.map Observation.Event.pure ++ later) ++ [.pure (.reorder 0 [])]) initial = _
    rw [← runHistories_singleton,runHistories_append,runHistories_append,runHistories_singleton,prefixRun]
    change (do
      let intermediate ← runHistories dependencies 65 later [prefixHistory]
      runHistories dependencies 65 [.pure (.reorder 0 [])] intermediate) = _
    rw [runHistories_singleton,suffixRun]
    exact run_final_reorder dependencies 64 terminal
  · simp only [List.map_map,Function.comp_def,finalizeHistory_coefficient]
    change ((terminal.map fun history => history.operator 0 0 * star (history.operator 0 0) *
      rawOutcomeWeight program outcome history.values).sum) = _
    change ((terminal.map fun history => history.operator 0 0 * star (history.operator 0 0) *
      rawOutcomeWeight program outcome history.values).sum) = _ at marginal
    rw [marginal,finished.readout_width]
    simp only [emptyValues,List.nil_append]
    rw [list_sum_range]
    have rawConditional : ∀ row,
        program.classicalOutputs.mapM (RawInstrument.value (trace.basisWrites row)) = some outcome ↔
        target.circuit.measurements.map (fun axis => bit row (finished.final.locations.idxOf axis) == 1) = outcome := by
      intro row
      simp only [writes,Option.some.injEq]
    have sameWord (row : Nat) : target.circuit.measurements.map (fun axis => bit row axis == 1) =
        target.circuit.measurements.map (fun axis => bit (gather row finished.final.locations)
          (finished.final.locations.idxOf axis) == 1) := by
      simpa only [List.map_map,Function.comp_def] using
        congrArg (List.map (fun code : Nat => code == 1)) (finished.readout.measurement_word layout.1 row)
    let amplitudes := fun row (_ : Unit) => prefixHistory.operator row 0
    have compare := reference_marginal_on_placed_frame finished.final.locations target.circuit.qubits
      layout.1 layout.2
      (fun row => target.circuit.measurements.map (fun axis => bit row axis == 1) = outcome)
      (fun row => target.circuit.measurements.map
        (fun axis => bit row (finished.final.locations.idxOf axis) == 1) = outcome)
      (fun row _ => by dsimp only; rw [sameWord row]) amplitudes () ()
    rw [← finished.readout.allGates,embedded]
    refine Eq.trans ?_ compare.symm
    apply Finset.sum_congr rfl
    intro row _
    simp only [rawOutcomeWeight,rawConditional]
    split <;> simp [amplitudes]

#print axioms FinishedTrace.exact_terminal_output


/-- Derive the exact original terminal ownership state from successful
verification of this same Raw program. The only prefix premise is the
literal source and physical correspondence of its checked alignment. -/
theorem FinishedTrace.exact_verified_terminal_output {bytes capacity}
    {target : QleisliKernel.Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Observation.Program} {dependencies connected reserved synthesis suffix events}
    (finished : QleisliKernel.Target.CanonicalOpenQasmPlacement.FinishedTrace
      program dependencies target connected reserved synthesis suffix)
    (aligned : PrefixAlignment dependencies program target.circuit finished.final events)
    {checked : QleisliKernel.Raw.Observation.Checked}
    (verified : QleisliKernel.Qirf.RuntimeInterval.Computed
      (QleisliKernel.Raw.Observation.verify dependencies program) checked)
    (classical outcome : List Bool) :
    ∃ histories, ObservingAction.program dependencies program classical = some histories ∧
      ((histories.map fun history =>
        history.operator 0 0 * star (history.operator 0 0) * rawOutcomeWeight program outcome history.values).sum) =
      ∑ physical ∈ Finset.range (2^target.circuit.qubits),
        if target.circuit.measurements.map (fun axis => bit physical axis == 1) = outcome then
          resetPrefix target.circuit target.circuit.gates.length physical *
            star (resetPrefix target.circuit target.circuit.gates.length physical)
        else 0 := by
  have closed : program.inputs = [] := List.isEmpty_iff.mp finished.closed.1
  obtain ⟨work,left,ran⟩ := verified
  have owned := QleisliKernel.Raw.Observation.verify_ownershipSafe dependencies program checked work left ran
  obtain ⟨entry,exit,suffixOwn,same⟩ := Qleisli.RuntimeTerminalRawMarginal.ownership_after_closed_pure_prefix
    owned closed (aligned.read_prefix closed)
  exact FinishedTrace.exact_terminal_output finished aligned suffixOwn same classical outcome

#print axioms FinishedTrace.exact_verified_terminal_output


open QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5
open QleisliKernel.Protocol.NativeContext (Decision)

/-- Exact realization of the original selected root in one accepted terminal
packet. The complex column before measurement retains phase and physical
scratch, and the final marginal keeps all original hidden outcomes. -/
structure TerminalCorrespondence {bytes : ByteArray} (checked : PlacementPacket.Checked bytes)
    (classical outcome : List Bool) : Prop where
  framed : PlacementPacket.split bytes = .ok checked.parts
  source : ∃ afterPlan afterSource,
    QleisliKernel.Protocol.ExecutionView.Packet.read checked.parts.source = .ok checked.source.1 ∧
    checked.source.1.scope = .execution ∧
    Nonempty (QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5.Binding
      checked.source.1.original checked.source.1.graph checked.source.2 afterPlan afterSource)
  root : checked.source.2.artifact.programs[checked.source.2.artifact.root]? =
    some checked.source.2.checked.root.program
  decoded : decode checked.parts.target = some checked.target.circuit
  reset : QleisliKernel.Target.CanonicalOpenQasmResources.ResetRead checked.parts.target checked.target.circuit
  column :
    let root := checked.source.2.checked.root
    let state := checked.placement.trace.final
    let circuit := checked.target.circuit
    ∃ events : List Event,
      Observation.readOps 65 (RawTrace.initial root.program.inputs) (root.program.operations.take state.rawIndex) =
        some (state.raw,events.map Observation.Event.pure) ∧
      resetPrefix circuit circuit.gates.length = physicalColumn state.locations
        (RawAction.events root.dependencies events (fun row => (ObservingAction.initial []).operator row 0))
  outcomes :
    let root := checked.source.2.checked.root
    let circuit := checked.target.circuit
    ∃ histories, ObservingAction.program root.dependencies root.program classical = some histories ∧
      ((histories.map fun history =>
        history.operator 0 0 * star (history.operator 0 0) *
          rawOutcomeWeight root.program outcome history.values).sum) =
      ∑ physical ∈ Finset.range (2^circuit.qubits),
        if circuit.measurements.map (fun axis => bit physical axis == 1) = outcome then
          resetPrefix circuit circuit.gates.length physical * star (resetPrefix circuit circuit.gates.length physical)
        else 0

/-- The original source check and each accepted replay step give the exact
column and final distribution of these same decoded target bytes. -/
theorem PlacementPacket.Checked.exact_verified_terminal_output {bytes : ByteArray}
    (checked : PlacementPacket.Checked bytes) {work left : Nat}
    (ran : (PlacementPacket.check bytes).run work = (.ok checked,left))
    (classical outcome : List Bool) : TerminalCorrespondence checked classical outcome := by
  let original := checked.source.2
  obtain ⟨_,_,fresh⟩ := original.checked.fresh
  have actual := QleisliKernel.Qirf.Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ fresh
  obtain ⟨_,_,verified⟩ := actual.verification
  have closed := List.isEmpty_iff.mp checked.placement.trace.closed.1
  have noClassical := List.isEmpty_iff.mp checked.placement.trace.closed.2
  obtain ⟨events,aligned⟩ := aligned_checked_placement checked.placement (fun occurrence _ alignedPrefix width declared =>
    PrefixAlignment.extend_replay checked.target.original occurrence alignedPrefix width declared
      (structural_replay_sound checked.target.original closed noClassical verified)
      (protected_replay_sound checked.target.original closed noClassical verified))
  refine ⟨checked.framed,checked.source_bound work left ran,actual.original,checked.target.original,
    QleisliKernel.Target.CanonicalOpenQasmResources.decode_reset checked.target.original,?_,?_⟩
  · refine ⟨events,aligned.read_prefix closed,?_⟩
    rw [← checked.placement.trace.readout.allGates]
    exact aligned.reset_column
  · exact Qleisli.TerminalPlacement.FinishedTrace.exact_verified_terminal_output checked.placement.trace aligned
      actual.verification classical outcome

#print axioms PlacementPacket.Checked.exact_verified_terminal_output

/-- The actual native placement decision returns the decoded counts for the
same checked specialization and target whose behavior is verified above. -/
theorem native_terminal_correspondence (product : String) (bytes : ByteArray)
    (decision : Decision .openQasmPlacement) (work left : Nat)
    (ran : (QleisliKernel.Protocol.NativeContext.run .openQasmPlacement product bytes).run work =
      (.ok decision,left)) (classical outcome : List Bool) :
    ∃ checked : PlacementPacket.Checked bytes,
      (PlacementPacket.check bytes).run work = (.ok checked,left) ∧
      TerminalCorrespondence checked classical outcome ∧
      let counts := checked.target.circuit.counts
      (decode checked.parts.target).map QleisliKernel.Target.CanonicalOpenQasmResources.Circuit.counts = some counts ∧
      checked.placement.trace.recorded.peakWires ≤ counts.reserved ∧
      counts.reserved ≤ checked.proposal.capacity ∧
      (QleisliKernel.Protocol.NativeContext.reply .openQasmPlacement work (.ok decision) left).lines.drop 6 =
        [work-left,counts.reserved,counts.reset,counts.gates,counts.swaps,
          counts.tGates,counts.measurements].map toString := by
  obtain ⟨checked,accepted,_,rfl⟩ :=
    QleisliKernel.Protocol.NativeContext.run_openqasm_placement_binding product bytes decision work left ran
  exact ⟨checked,accepted,PlacementPacket.Checked.exact_verified_terminal_output checked accepted classical outcome,
    checked.target_counts,checked.covers_workspace_peak,checked.target.capacityBound,rfl⟩

#print axioms native_terminal_correspondence

end Qleisli.TerminalPlacement
