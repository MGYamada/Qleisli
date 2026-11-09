import Qleisli.RuntimeNamedBlockEncoding
import Qleisli.RuntimeOriginalBranch
import Qleisli.RuntimeTraceSpectators

/-! Parent and child traces of an original named call share the selected
ports. The frame relation follows the actual wire lists across erasure
and allocation, including spectators with no wires.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceFrames
open QleisliKernel QleisliKernel.Qirf
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface take insert axes)
open Semantics.Observation (remaining)
open Raw.ObservationAgreement (Reader readStep)

abbrev WireOrder (ports : List Port) := ports.flatMap Port.wires

structure Partition (parent child : Interface) (spectators : List Port) : Prop where
  live : parent.live.Perm (child.live ++ spectators)
  frame : parent.frame.Perm (child.frame ++ WireOrder spectators)

/-- The exact live port wires cover the native frame once. -/
theorem native_wires (state : Raw.State) (valid : Raw.stateValid state = true) :
    (WireOrder state.live).Perm state.frame := by
  have facts := Raw.Ownership.valid state valid
  obtain ⟨ordered,permutation,sublist⟩ := List.subperm_iff.mp (facts.exclusive.subperm facts.covered)
  have same := sublist.eq_of_length (facts.count.trans permutation.length_eq.symm)
  have equal : WireOrder state.live = ordered := same
  rw [equal]
  exact permutation

theorem Partition.of_native (parent child : Raw.State) (spectators : List Port)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    (live : parent.live.Perm (child.live ++ spectators)) :
    Partition parent.reference child.reference spectators := by
  refine ⟨live,?_⟩
  have wires := live.flatMap_right Port.wires
  simp only [List.flatMap_append] at wires
  exact (native_wires parent parentValid).symm.trans
    (wires.trans ((native_wires child childValid).append_right _))

/-- The partition starts at the original argument assignment. Its complement
is the same complete source owner map used in the sparse boundary proof. -/
theorem original_entry
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (sameBindings : checked.bindings = before.bindings) :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    Partition scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference
      (spectators.map (·.port)) := by
  intro spectators
  have order := RuntimeNamedBlockEncoding.original_named_partition_geometry scope boundary checked sameBindings
  have ports := checked.complete.symm.trans (order.symm.map RuntimeOwnerMap.Binding.port)
  rw [List.map_append,← RuntimeNamedFrameAxes.mixed_bound_ports scope boundary] at ports
  have childEntry := RuntimeNamedFrameAxes.initialized scope.prepared.inputRead
  have childPorts := congrArg Interface.live (RuntimeNamedFrameAxes.mixedAxes_input scope).2.2.1
  apply Partition.of_native _ _ _ scope.interval.history.1 childEntry.2.1
  change scope.interval.before.quantum.live.Perm
    (scope.prepared.block.entry.quantum.reference.live ++ spectators.map (·.port))
  rw [childPorts]
  exact ports

/-- A wire of the local frame retains its exact position in the parent. -/
theorem wire_positions (parent child : Interface) (wires : List Nat)
    (inside : wires ⊆ child.frame) :
    (axes child wires).mapM (fun i => (child.frame.map parent.frame.idxOf)[i]?) =
      some (axes parent wires) := by
  induction wires with
  | nil => rfl
  | cons first rest ih =>
    have firstIn := inside List.mem_cons_self
    have lookup : (child.frame.map parent.frame.idxOf)[child.frame.idxOf first]? =
        some (parent.frame.idxOf first) := by
      rw [List.getElem?_map,RuntimeNamedFrameAxes.wireLookup _ firstIn]
      rfl
    have tail := ih (fun _ member => inside (List.mem_cons_of_mem _ member))
    simp only [axes] at tail
    simp only [axes,List.map_cons,List.mapM_cons,lookup,tail,bind,Option.bind,pure]

def removed (before taken : Interface) (port : Port) : Interface :=
  {taken with frame := remaining before port.wires}

def allocated (state : Interface) (output wire : Nat) : Interface :=
  {insert state output [wire] with frame := state.frame ++ [wire]}

theorem Partition.insert_append {parent child : Interface} {spectators : List Port}
    (relation : Partition parent child spectators) (output : Nat) (wires extra : List Nat) :
    Partition {insert parent output wires with frame := parent.frame ++ extra}
      {insert child output wires with frame := child.frame ++ extra} spectators := by
  refine ⟨(RuntimeTraceSpectators.insert_spectators _ _ _ relation.live output wires).1,?_⟩
  change (parent.frame ++ extra).Perm ((child.frame ++ extra) ++ WireOrder spectators)
  exact (relation.frame.append_right _).trans (by
    simpa only [List.append_assoc] using
      (List.perm_append_comm : (WireOrder spectators ++ extra).Perm (extra ++ WireOrder spectators)).append_left child.frame)

theorem Partition.allocate {parent child : Interface} {spectators : List Port}
    (relation : Partition parent child spectators) (output wire : Nat) :
    Partition (allocated parent output wire) (allocated child output wire) spectators :=
  relation.insert_append output [wire] [wire]

/-- Both traces append the same freshly allocated wire at their own end. -/
theorem allocation_events {parent child : Interface} {spectators : List Port}
    (relation : Partition parent child spectators) (output wire : Nat) :
    Partition (allocated parent output wire) (allocated child output wire) spectators ∧
      Semantics.RawTrace.step parent (.init0 output wire) =
        some (allocated parent output wire,[.init0 parent.frame.length]) ∧
      Semantics.RawTrace.step child (.init0 output wire) =
        some (allocated child output wire,[.init0 child.frame.length]) :=
  ⟨relation.allocate output wire,rfl,rfl⟩

/-- The port returned by the literal take belongs to that exact input. -/
theorem taken_member {state after : Interface} {input : Nat} {port : Port}
    (read : take state input = some (port,after)) : port ∈ state.live := by
  unfold take at read
  obtain ⟨found,lookup,rest⟩ := Option.bind_eq_some_iff.mp read
  have same : found = port := congrArg Prod.fst (Option.some.inj rest)
  exact same ▸ List.mem_of_find?_eq_some lookup

/-- Erasure uses the exact same Port in the caller and child. The surviving
frame still has the same untouched spectator wires in its partition. -/
theorem original_take (parent child : Raw.State) (spectators : List Port)
    (relation : Partition parent.reference child.reference spectators)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    {input : Nat} {port : Port} {childTaken : Interface}
    (read : take child.reference input = some (port,childTaken)) :
    ∃ parentTaken,
      take parent.reference input = some (port,parentTaken) ∧
      Partition (removed parent.reference parentTaken port) (removed child.reference childTaken port) spectators ∧
      (axes child.reference port.wires).mapM (fun i => (child.frame.map parent.frame.idxOf)[i]?) =
        some (axes parent.reference port.wires) := by
  have parentFacts := Raw.Ownership.valid parent parentValid
  have childFacts := Raw.Ownership.valid child childValid
  obtain ⟨parentTaken,parentRead,live,_,_,_⟩ := RuntimeTraceSpectators.take_spectators
    _ _ _ relation.live parentFacts.owners read
  have portMember := taken_member read
  have selectedWires : port.wires ⊆ child.frame := by
    intro wire member
    exact childFacts.covered wire (List.mem_flatMap.mpr ⟨port,portMember,member⟩)
  have unique := relation.frame.nodup_iff.mp parentFacts.frame
  have untouched : (WireOrder spectators).filter (fun wire => !port.wires.contains wire) =
      WireOrder spectators := by
    apply List.filter_eq_self.mpr
    intro wire member
    have apart : wire ∉ port.wires := fun consumed =>
      (List.nodup_append.mp unique).2.2 wire (selectedWires consumed) wire member rfl
    simp [apart]
  have frames : (remaining parent.reference port.wires).Perm
      (remaining child.reference port.wires ++ WireOrder spectators) := by
    simpa only [remaining,List.filter_append,untouched] using
      relation.frame.filter (fun wire => !port.wires.contains wire)
  exact ⟨parentTaken,parentRead,⟨live,frames⟩,wire_positions parent.reference child.reference port.wires selectedWires⟩

def erasure (before : Interface) (port : Port) (measured : Option Nat) :
    Semantics.Observation.Event :=
  .erase before.frame.length (axes before port.wires) measured

/-- Successful literal reads of measurement and discard on the same written
token expose the same consumed port, physical axis correspondence and the
exact public SSA output. Reset uses the same erasure followed by allocation. -/
theorem erasure_events (parent child : Raw.State) (spectators : List Port)
    (relation : Partition parent.reference child.reference spectators)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    (parentReader childReader : Reader)
    {input : Nat} {port : Port} {childTaken : Interface}
    (read : take child.reference input = some (port,childTaken)) :
    ∃ parentTaken,
      let p := removed parent.reference parentTaken port
      let c := removed child.reference childTaken port
      Partition p c spectators ∧
      (axes child.reference port.wires).mapM (fun i => (child.frame.map parent.frame.idxOf)[i]?) =
        some (axes parent.reference port.wires) ∧
      (∀ output,
        readStep parentReader parent.reference (.measure input output) =
          some (p,[erasure parent.reference port (some output)]) ∧
        readStep childReader child.reference (.measure input output) =
          some (c,[erasure child.reference port (some output)])) ∧
      (readStep parentReader parent.reference (.discard input) =
          some (p,[erasure parent.reference port none]) ∧
        readStep childReader child.reference (.discard input) =
          some (c,[erasure child.reference port none])) ∧
      ∀ output wire,
        Partition (allocated p output wire) (allocated c output wire) spectators ∧
        readStep parentReader parent.reference (.reset input output wire) =
          some (allocated p output wire,[erasure parent.reference port none,.pure (.init0 p.frame.length)]) ∧
        readStep childReader child.reference (.reset input output wire) =
          some (allocated c output wire,[erasure child.reference port none,.pure (.init0 c.frame.length)]) := by
  obtain ⟨parentTaken,parentRead,frames,coordinates⟩ := original_take parent child spectators relation parentValid childValid read
  refine ⟨parentTaken,frames,coordinates,?_,?_,?_⟩
  · intro output
    simp [readStep,parentRead,read,removed,erasure]
  · simp [readStep,parentRead,read,removed,erasure]
  · intro output wire
    refine ⟨frames.allocate output wire,?_⟩
    simp [readStep,parentRead,read,removed,allocated,erasure,Semantics.RawTrace.insert]

/-- The original basis lift expands each physical frame by the same new
wires. The actual native results determine the pre/post operand axes and
retain the same basis table. -/
theorem basis_lift_events {signatures : List Semantics.Finite.Basis}
    (parent child : Raw.State) (spectators : List Port)
    (relation : Partition parent.reference child.reference spectators)
    (input output : Nat) (wires table : List Nat) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step signatures parent (.liftBasis input output wires table) = .ok parentAfter)
    (childRead : Raw.step signatures child (.liftBasis input output wires table) = .ok childAfter) :
    ∃ port : Port,
      Partition parentAfter.state.reference childAfter.state.reference spectators ∧
      parentAfter.state.frame = parent.frame ++ wires.drop port.bits ∧
      childAfter.state.frame = child.frame ++ wires.drop port.bits ∧
      port.wires ⊆ child.frame ∧ wires ⊆ childAfter.state.frame ∧
      parentAfter.events = [.liftBasis parent.frame.length parentAfter.state.frame.length
        (axes parent.reference port.wires) (axes parentAfter.state.reference wires) table] ∧
      childAfter.events = [.liftBasis child.frame.length childAfter.state.frame.length
        (axes child.reference port.wires) (axes childAfter.state.reference wires) table] ∧
      (axes child.reference port.wires).mapM (fun i => (child.frame.map parent.frame.idxOf)[i]?) =
        some (axes parent.reference port.wires) ∧
      (axes childAfter.state.reference wires).mapM
        (fun i => (childAfter.state.frame.map parentAfter.state.frame.idxOf)[i]?) =
        some (axes parentAfter.state.reference wires) := by
  obtain ⟨parentValid,_,_⟩ := Raw.step_conditions _ _ _ _ parentRead
  obtain ⟨childValid,_,childAfterValid⟩ := Raw.step_conditions _ _ _ _ childRead
  have parentFacts := Raw.Ownership.valid parent parentValid
  have childFacts := Raw.Ownership.valid child childValid
  have childTrace := Raw.step_reference _ _ _ _ childRead
  have parentTrace := Raw.step_reference _ _ _ _ parentRead
  simp only [Semantics.RawTrace.step] at childTrace
  obtain ⟨⟨port,childTaken⟩,childTake,childResult⟩ := Option.bind_eq_some_iff.mp childTrace
  obtain ⟨parentTaken,parentTake,live,parentFrame,childFrame,_⟩ :=
    RuntimeTraceSpectators.take_spectators _ _ _ relation.live parentFacts.owners childTake
  let extra := wires.drop port.bits
  let p : Interface := {insert parentTaken output wires with frame := parent.frame ++ extra}
  let c : Interface := {insert childTaken output wires with frame := child.frame ++ extra}
  have pResult : (p,[Semantics.Raw.Event.liftBasis parent.frame.length p.frame.length
      (axes parent.reference port.wires) (axes p wires) table]) = (parentAfter.state.reference,parentAfter.events) := by
    apply Option.some.inj
    simpa only [Semantics.RawTrace.step,parentTake,bind,Option.bind,pure,p,extra,axes] using parentTrace
  have cResult : (c,[Semantics.Raw.Event.liftBasis child.frame.length c.frame.length
      (axes child.reference port.wires) (axes c wires) table]) = (childAfter.state.reference,childAfter.events) :=
    Option.some.inj childResult
  obtain ⟨pState,pEvents⟩ := Prod.mk.inj pResult
  obtain ⟨cState,cEvents⟩ := Prod.mk.inj cResult
  have taken : Partition parentTaken childTaken spectators :=
    ⟨live,by rw [parentFrame,childFrame]; exact relation.frame⟩
  have localInput : port.wires ⊆ child.frame := by
    intro wire member
    exact childFacts.covered wire (List.mem_flatMap.mpr ⟨port,taken_member childTake,member⟩)
  have localOutput : wires ⊆ childAfter.state.frame := by
    have portIn : (⟨output,wires,wires.length⟩ : Port) ∈ childAfter.state.reference.live := by
      rw [← cState]
      simp [c,Semantics.RawTrace.insert]
    intro wire member
    exact (Raw.Ownership.valid _ childAfterValid).covered wire (List.mem_flatMap.mpr ⟨_,portIn,member⟩)
  refine ⟨port,?_,(congrArg Interface.frame pState).symm,(congrArg Interface.frame cState).symm,
    localInput,localOutput,?_,?_,wire_positions parent.reference child.reference _ localInput,
    wire_positions parentAfter.state.reference childAfter.state.reference _ localOutput⟩
  · rw [← pState,← cState]
    simpa only [p,c,parentFrame,childFrame] using taken.insert_append output wires extra
  · change parentAfter.events = [.liftBasis parent.frame.length parentAfter.state.reference.frame.length
      (axes parent.reference port.wires) (axes parentAfter.state.reference wires) table]
    rw [← pState]
    exact pEvents.symm
  · change childAfter.events = [.liftBasis child.frame.length childAfter.state.reference.frame.length
      (axes child.reference port.wires) (axes childAfter.state.reference wires) table]
    rw [← cState]
    exact cEvents.symm

/-- Unit introduction retains the new zero-width port in both owner lists. -/
theorem pack_unit_events {parent child : Interface} {spectators : List Port}
    (relation : Partition parent child spectators) (output : Nat) :
    Partition (insert parent output []) (insert child output []) spectators ∧
      Semantics.RawTrace.step parent (.packUnit output) = some (insert parent output [],[]) ∧
      Semantics.RawTrace.step child (.packUnit output) = some (insert child output [],[]) := by
  exact ⟨⟨(RuntimeTraceSpectators.insert_spectators _ _ _ relation.live output []).1,relation.frame⟩,rfl,rfl⟩

/-- A successful Unit elimination removes the same zero-width port, including
its owner identity, from both readers. -/
theorem unpack_unit_events {parent child : Interface} {spectators : List Port}
    (relation : Partition parent child spectators) (unique : (parent.live.map (·.token)).Nodup)
    {input : Nat} {childAfter : Interface} {events : List Semantics.Raw.Event}
    (read : Semantics.RawTrace.step child (.unpackUnit input) = some (childAfter,events)) :
    ∃ parentAfter, Semantics.RawTrace.step parent (.unpackUnit input) = some (parentAfter,events) ∧
      Partition parentAfter childAfter spectators ∧
      parentAfter.frame = parent.frame ∧ childAfter.frame = child.frame ∧ events = [] := by
  simp only [Semantics.RawTrace.step] at read
  obtain ⟨⟨port,childTaken⟩,childTake,finished⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨parentTaken,parentTake,live,parentFrame,childFrame,_⟩ :=
    RuntimeTraceSpectators.take_spectators _ _ _ relation.live unique childTake
  dsimp only at finished
  split at finished
  next zero =>
    have equal := Option.some.inj finished
    rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
    refine ⟨parentTaken,?_,⟨live,?_⟩,parentFrame,childFrame,rfl⟩
    · simp only [Semantics.RawTrace.step,parentTake,bind,Option.bind,if_pos zero,pure]
    · rw [parentFrame,childFrame]
      exact relation.frame
  next _ => cases finished

/-- Both native branches use the complete written phi list. If their
actual left outputs are related by a retained spectator partition, the
two successful checks force that partition's spectator list to be empty. -/
theorem branch_has_no_spectators
    {dependencies parentProgram childProgram parentBlock childBlock parentOffset childOffset}
    (parent : @RuntimeInterval.Branch dependencies parentProgram parentBlock parentOffset)
    (child : @RuntimeInterval.Branch dependencies childProgram childBlock childOffset)
    (samePhis : parent.quantum = child.quantum)
    {spectators : List Port}
    (live : parent.thenState.quantum.live.Perm (child.thenState.quantum.live ++ spectators)) :
    spectators = [] := by
  have parentOK := (RuntimeOriginalBranch.original_branch_phi_checks parent).1
  have childOK := (RuntimeOriginalBranch.original_branch_phi_checks child).1
  simp only [Raw.Observation.phiValid,Bool.and_eq_true,beq_iff_eq] at parentOK childOK
  have parentLength : parent.quantum.length = parent.thenState.quantum.live.length := by
    exact parentOK.1.1.1.1.2
  have childLength : child.quantum.length = child.thenState.quantum.live.length := by
    exact childOK.1.1.1.1.2
  have equalLength := parentLength.symm.trans ((congrArg List.length samePhis).trans childLength)
  have partition := live.length_eq
  rw [List.length_append,equalLength] at partition
  exact List.length_eq_zero_iff.mp (by omega)

private theorem original_call_branch_operation
    {dependencies program block start count inputs ordinary effect offset}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (parent : RuntimeInterval.Branch block (start+offset))
    (child : RuntimeInterval.Branch scope.prepared.block offset) :
    Semantics.Observation.Op.branch parent.condition parent.thenOps parent.elseOps parent.quantum parent.classical =
      .branch child.condition child.thenOps child.elseOps child.quantum child.classical := by
  have range := child.interval.range
  change offset+1 ≤ ((block.operations.drop start).take count).length at range
  rw [List.length_take] at range
  have inside : offset < count := by omega
  have original := child.original
  change ((block.operations.drop start).take count)[offset]? = _ at original
  rw [List.getElem?_take_of_lt inside,List.getElem?_drop] at original
  exact Option.some.inj (parent.original.symm.trans original)

/-- For a branch at the original position inside a named call, the two
checked records refer to the same written phi list. -/
theorem original_call_branch_has_no_spectators
    {dependencies program block start count inputs ordinary effect offset}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (parent : RuntimeInterval.Branch block (start+offset))
    (child : RuntimeInterval.Branch scope.prepared.block offset)
    {spectators : List Port}
    (live : parent.thenState.quantum.live.Perm (child.thenState.quantum.live ++ spectators)) :
    spectators = [] := by
  have same := Semantics.Observation.Op.branch.inj (original_call_branch_operation scope parent child)
  exact branch_has_no_spectators parent child same.2.2.2.1 live

private theorem port_lookup_perm {parent child : List Port} (live : parent.Perm child)
    (parentUnique : (parent.map Port.token).Nodup) (childUnique : (child.map Port.token).Nodup)
    (token : Nat) :
    parent.find? (fun p => p.token == token) = child.find? (fun p => p.token == token) := by
  cases localRead : child.find? (fun p => p.token == token) with
  | some port =>
    have key : port.token = token :=
      beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == token) localRead)
    simpa only [key] using RuntimeNamedFrameAxes.tokenLookup parent port parentUnique
      (live.mem_iff.mpr (List.mem_of_find?_eq_some localRead))
  | none =>
    cases parentRead : parent.find? (fun p => p.token == token) with
    | none => rfl
    | some port =>
      have key : port.token = token :=
        beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == token) parentRead)
      have actual := RuntimeNamedFrameAxes.tokenLookup child port childUnique
        (live.mem_iff.mp (List.mem_of_find?_eq_some parentRead))
      rw [key,localRead] at actual
      cases actual

/-- The same written phi tokens select the same ordered port wires. -/
theorem branch_wires {parent child : Raw.State} (live : parent.live.Perm child.live)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    (phis : List Semantics.Observation.QuantumPhi) (choice : Bool) :
    Semantics.Observation.phiWires parent.reference phis choice =
      Semantics.Observation.phiWires child.reference phis choice := by
  unfold Semantics.Observation.phiWires
  apply List.flatMap_congr
  intro phi _
  have exactPort := port_lookup_perm live (Raw.Ownership.valid parent parentValid).owners
    (Raw.Ownership.valid child childValid).owners (if choice then phi.thenToken else phi.elseToken)
  change parent.reference.live.find? _ = child.reference.live.find? _ at exactPort
  rw [exactPort]

/-- Each original branch rejoins on the same ordered wire list. The two
actual readers may use different pre-join axis numbers, but the emitted
classical condition, phi declarations and complete output interface agree. -/
theorem original_call_branch_join
    {dependencies program block start count inputs ordinary effect offset}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (parent : RuntimeInterval.Branch block (start+offset))
    (child : RuntimeInterval.Branch scope.prepared.block offset)
    {spectators : List Port}
    (left : parent.thenState.quantum.live.Perm (child.thenState.quantum.live ++ spectators))
    (right : parent.elseState.quantum.live.Perm (child.elseState.quantum.live ++ spectators)) :
    spectators = [] ∧ parent.condition = child.condition ∧ parent.classical = child.classical ∧
      parent.interval.after.quantum.reference = child.interval.after.quantum.reference ∧
      Semantics.Observation.phiWires parent.thenState.quantum.reference parent.quantum true =
        Semantics.Observation.phiWires child.thenState.quantum.reference child.quantum true ∧
      Semantics.Observation.phiWires parent.elseState.quantum.reference parent.quantum false =
        Semantics.Observation.phiWires child.elseState.quantum.reference child.quantum false := by
  have same := Semantics.Observation.Op.branch.inj (original_call_branch_operation scope parent child)
  have quantum := same.2.2.2.1
  have empty := branch_has_no_spectators parent child quantum left
  subst spectators
  simp only [List.append_nil] at left right
  obtain ⟨p⟩ := RuntimeOriginalBranch.original_branch_events parent
  obtain ⟨c⟩ := RuntimeOriginalBranch.original_branch_events child
  obtain ⟨_,_,pLeft⟩ := parent.thenRead
  obtain ⟨_,_,pRight⟩ := parent.elseRead
  obtain ⟨_,_,cLeft⟩ := child.thenRead
  obtain ⟨_,_,cRight⟩ := child.elseRead
  refine ⟨rfl,same.1,same.2.2.2.2,p.joined.trans ((congrArg Semantics.Observation.phiInterface quantum).trans c.joined.symm),?_,?_⟩
  · rw [quantum]
    exact branch_wires left (Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ pLeft).1
      (Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ cLeft).1 _ true
  · rw [quantum]
    exact branch_wires right (Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ pRight).1
      (Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ cRight).1 _ false

#print axioms original_entry
#print axioms erasure_events
#print axioms basis_lift_events
#print axioms branch_has_no_spectators
#print axioms original_call_branch_has_no_spectators
#print axioms original_call_branch_join
end Qleisli.RuntimeCallTraceFrames
