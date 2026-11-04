import Qleisli.RuntimeNamedGateLift
import Qleisli.RuntimeSourcePrimitiveAction
import Qleisli.FiniteMatrixAction
import Qleisli.RuntimeFiniteTargetScatter

/-! Compose the actual primitive's original source/code action with its named
caller's literal Raw events. The same reconstructed one-circuit fragment and
its explicit final reorder connect the two equations; neither a caller matrix
nor an assumed intertwining outcome is an input. The encoded parent amplitude
retains an arbitrary spectator/reference fibre. Whole source-forest encoding
and the final caller output permutation remain separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedPrimitiveSourceLift
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
open Qleisli.Semantics.Exact Qleisli.RuntimeNamedGateLift

private theorem width_register (bits : Nat) : width (Raw.registerBasis bits) = bits := by
  induction bits with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp [Raw.registerBasis,Semantics.Raw.registerBasis,width] at ih ⊢
      omega

private theorem identity_action {Reference : Type} (dim : Nat) (initial : Matrix)
    (read : QleisliKernel.Exact.Matrix.identity dim = .ok initial)
    (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) (bound : row < dim) :
    action initial joint row reference = joint row reference := by
  obtain ⟨_,_rows,cols,entries⟩ := Qleisli.Exact.identity_meaning dim initial read
  unfold action
  rw [cols]
  calc
    _ = ((List.range dim).map (fun column => if row = column then joint column reference else 0)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro column member
      rw [entries row column bound (List.mem_range.mp member)]
      split <;> simp
    _ = joint row reference := Qleisli.Exact.range_delta_sum dim row (fun column => joint column reference) bound

private theorem reorder_mapping_action {Reference : Type} (dependencies : List Dependency)
    (bits : Nat) (axes : List Nat) (actual : Matrix)
    (read : RuntimeInterval.Computed (Raw.mapping bits bits
      ((List.range (2^bits)).map (fun label => gather label axes))) actual)
    (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) (bound : row < 2^bits) :
    action actual joint row reference = Qleisli.Semantics.RawAction.event dependencies (.reorder bits axes)
      (fun input => joint input reference) row := by
  obtain ⟨work,left,ran⟩ := read
  have shape := Raw.mapping_value _ _ _ _ _ _ ran
  have cols : actual.cols = 2^bits := congrArg Matrix.cols shape
  unfold action
  rw [cols]
  change _ = ((List.range (2^bits)).map
    (fun input => if gather input axes == row then joint input reference else 0)).sum
  apply Qleisli.Exact.sum_map_congr
  intro input member
  have inside := List.mem_range.mp member
  rw [Qleisli.Raw.mapping_meaning _ _ _ _ _ _ ran row input bound inside]
  by_cases same : gather input axes = row <;> simp [inside,same]

/-- Only receipts already present in the actual protected reconstruction.
The two matrix compositions include the original identity and final reorder. -/
private structure Reconstruction (dependencies : List Dependency) (bits : Nat)
    (steps : List Step) (axes : List Nat) (physical : Matrix) where
  initial : Matrix
  circuit : Matrix
  afterCircuit : Matrix
  reordered : Matrix
  initialRead : QleisliKernel.Exact.Matrix.identity (2^bits) = .ok initial
  circuitRead : RuntimeInterval.Computed (QleisliKernel.Finite.circuitMatrix dependencies (Raw.circuit bits steps)) circuit
  firstRead : ∃ work left, QleisliKernel.Exact.Matrix.compose circuit initial work = (.ok afterCircuit,left)
  reorderRead : RuntimeInterval.Computed (Raw.mapping bits bits
    ((List.range (2^bits)).map (fun label => gather label axes))) reordered
  lastRead : ∃ work left, QleisliKernel.Exact.Matrix.compose reordered afterCircuit work = (.ok physical,left)

private theorem reconstruction_receipts (dependencies : List Dependency) (program : Semantics.Raw.Program)
    (physical : Matrix) (bits : Nat) (steps : List Step) (axes : List Nat)
    (trace : Semantics.RawTrace.Prepared)
    (original : Semantics.RawTrace.run program = some trace)
    (inputBits : trace.inputBits = bits)
    (events : trace.events = [.circuit bits steps,.reorder bits axes])
    (read : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies program) physical) :
    Nonempty (Reconstruction dependencies bits steps axes physical) := by
  obtain ⟨work,left,ran⟩ := read
  unfold Raw.ProtectedEvaluation.reconstruct at ran
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨prepared,w₂,opened,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,w₄,identityRead,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₅,evolved,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  have sameTrace := Option.some.inj
    ((Raw.prepare_reference _ _ _ (lift_success _ _ _ _ opened).1).symm.trans original)
  have preparedBits : prepared.inputBits = bits :=
    (congrArg Semantics.RawTrace.Prepared.inputBits sameTrace).trans inputBits
  have preparedEvents : prepared.events = [.circuit bits steps,.reorder bits axes] :=
    (congrArg Semantics.RawTrace.Prepared.events sameTrace).trans events
  have initialRead : QleisliKernel.Exact.Matrix.identity (2^bits) = .ok initial := by
    simpa only [preparedBits] using arithmetic_success _ _ (lift_success _ _ _ _ identityRead).1
  rw [preparedEvents] at evolved
  simp only [List.foldlM_cons] at evolved
  obtain ⟨afterCircuit,middle,first,rest⟩ := bind_success _ _ _ _ _ evolved
  obtain ⟨final,beforeEnd,last,finished⟩ := bind_success _ _ _ _ _ rest
  have finalSame := (pure_success _ _ _ _ finished).1
  subst final
  unfold Raw.ProtectedEvaluation.evolve at first last
  obtain ⟨circuit,beforeFirstCompose,circuitEvent,firstCompose⟩ := bind_success _ _ _ _ _ first
  obtain ⟨reordered,beforeLastCompose,reorderEvent,lastCompose⟩ := bind_success _ _ _ _ _ last
  change (do
    guard (bits ≤ 6) .limit
    QleisliKernel.Finite.circuitMatrix dependencies (Raw.circuit bits steps)).run w₄ =
      (.ok circuit,beforeFirstCompose) at circuitEvent
  obtain ⟨_,circuitWork,_,circuitRead⟩ := bind_success _ _ _ _ _ circuitEvent
  change (do
    guard (bits ≤ 6) .limit
    Raw.mapping bits bits ((List.range (2^bits)).map (fun label => gather label axes))).run middle =
      (.ok reordered,beforeLastCompose) at reorderEvent
  obtain ⟨_,mappingWork,_,mappingRead⟩ := bind_success _ _ _ _ _ reorderEvent
  exact ⟨{
    initial := initial
    circuit := circuit
    afterCircuit := afterCircuit
    reordered := reordered
    initialRead := initialRead
    circuitRead := ⟨circuitWork,beforeFirstCompose,circuitRead⟩
    firstRead := ⟨beforeFirstCompose,middle,exactWork_success _ _ _ _ firstCompose⟩
    reorderRead := ⟨mappingWork,beforeLastCompose,mappingRead⟩
    lastRead := ⟨beforeLastCompose,beforeEnd,exactWork_success _ _ _ _ lastCompose⟩ }⟩

private theorem reconstruction_action (dependencies : List Dependency) (bits : Nat)
    (steps : List Step) (axes : List Nat) (physical : Matrix)
    (receipts : Reconstruction dependencies bits steps axes physical) :
    physical.rows = 2^bits ∧ physical.cols = 2^bits ∧
    steps.all (QleisliKernel.Finite.stepValid dependencies bits) = true ∧
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
      row < physical.rows →
      action physical joint row reference = Qleisli.Semantics.RawAction.event dependencies (.reorder bits axes)
        (Qleisli.Semantics.RawAction.circuit dependencies steps (fun input => joint input reference)) row := by
  obtain ⟨circuitWork,circuitLeft,circuitRead⟩ := receipts.circuitRead
  obtain ⟨firstWork,firstLeft,firstRead⟩ := receipts.firstRead
  obtain ⟨mappingWork,mappingLeft,mappingRead⟩ := receipts.reorderRead
  obtain ⟨lastWork,lastLeft,lastRead⟩ := receipts.lastRead
  have circuitShape := Qleisli.Finite.circuitMatrix_pull dependencies (Raw.circuit bits steps)
    receipts.circuit circuitWork circuitLeft circuitRead
  have circuitRows : receipts.circuit.rows = 2^bits := by
    simpa only [Raw.circuit,width_register] using circuitShape.1
  have mappingShape := Raw.mapping_value _ _ _ _ _ _ mappingRead
  have reorderRows : receipts.reordered.rows = 2^bits := congrArg Matrix.rows mappingShape
  have firstShape := Qleisli.Exact.compose_meaning _ _ _ _ _ firstRead
  have lastShape := Qleisli.Exact.compose_meaning _ _ _ _ _ lastRead
  have identityShape := Qleisli.Exact.identity_meaning _ _ receipts.initialRead
  have rows : physical.rows = 2^bits := lastShape.2.1.trans reorderRows
  have cols : physical.cols = 2^bits := lastShape.2.2.1.trans (firstShape.2.2.1.trans identityShape.2.2.1)
  have valid := (QleisliKernel.Finite.circuitMatrix_columns dependencies (Raw.circuit bits steps)
    receipts.circuit circuitWork circuitLeft circuitRead).1
  have stepsValid : steps.all (QleisliKernel.Finite.stepValid dependencies bits) = true := by
    simp only [QleisliKernel.Finite.circuitValid,Raw.circuit,width_register,Bool.and_eq_true] at valid
    tauto
  refine ⟨rows,cols,stepsValid,?_⟩
  intro Reference joint row reference bound
  have rowBound : row < 2^bits := by simpa only [rows] using bound
  have middleAction (input : Nat) (inside : input < 2^bits) :
      action receipts.afterCircuit joint input reference =
        Qleisli.Semantics.RawAction.circuit dependencies steps (fun i => joint i reference) input := by
    calc
      _ = action receipts.circuit (fun i ref => action receipts.initial joint i ref) input reference :=
        Qleisli.Exact.compose_action _ _ _ _ _ firstRead joint input reference (by simpa only [circuitRows] using inside)
      _ = Qleisli.Semantics.RawAction.circuit dependencies steps
          (fun i => action receipts.initial joint i reference) input :=
        Qleisli.Finite.circuitMatrix_action dependencies (Raw.circuit bits steps) receipts.circuit
          circuitWork circuitLeft circuitRead (fun i ref => action receipts.initial joint i ref)
          input reference (by simpa only [circuitRows] using inside)
      _ = _ := Qleisli.Finite.rawCircuit_congr dependencies bits steps _ _ stepsValid
        (fun i h => identity_action _ _ receipts.initialRead joint i reference h) input inside
  calc
    _ = action receipts.reordered (fun i ref => action receipts.afterCircuit joint i ref) row reference :=
      Qleisli.Exact.compose_action _ _ _ _ _ lastRead joint row reference (by simpa only [reorderRows] using rowBound)
    _ = Qleisli.Semantics.RawAction.event dependencies (.reorder bits axes)
        (fun input => action receipts.afterCircuit joint input reference) row :=
      reorder_mapping_action dependencies bits axes receipts.reordered receipts.reorderRead
        (fun i ref => action receipts.afterCircuit joint i ref) row reference rowBound
    _ = _ := by
      change ((List.range (2^bits)).map (fun input =>
        if gather input axes == row then action receipts.afterCircuit joint input reference else 0)).sum = _
      apply Qleisli.Exact.sum_map_congr
      intro input member
      rw [middleAction input (List.mem_range.mp member)]

private theorem fragment_trace {dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents}
    (facts : Facts dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents) :
    Semantics.RawTrace.run (RuntimePureInterval.fragment [port] operations [output]) =
      some ⟨⟨[⟨output,port.wires,port.wires.length⟩],port.wires⟩,
        [.circuit port.wires.length form.tape,
          .reorder port.wires.length (port.wires.map port.wires.idxOf)],port.wires.length⟩ := by
  have frame := congrArg Semantics.RawTrace.Interface.frame facts.childEntry
  change localBefore.frame = port.wires at frame
  have actual : RuntimeLocalEvents.trace ⟨[port],port.wires⟩ operations =
      some ⟨⟨[⟨output,port.wires,port.wires.length⟩],port.wires⟩,
        [.circuit port.wires.length form.tape],port.wires.length⟩ := by
    simpa only [facts.childEntry,facts.childInterface,facts.childCircuit,frame] using facts.childTrace
  change operations.foldlM Semantics.RawTrace.advance
    ⟨⟨[port],port.wires⟩,[],port.wires.length⟩ = _ at actual
  have initial : Semantics.RawTrace.initial [port] = ⟨[port],port.wires⟩ := by
    simp only [Semantics.RawTrace.initial,List.flatMap_singleton]
  unfold Semantics.RawTrace.run
  simp only [RuntimePureInterval.fragment,initial,actual,bind,Option.bind,pure]
  simp [Semantics.RawTrace.finish,Semantics.RawTrace.axes]

private theorem scatter_overwrite (base first second : Nat) (axes : List Nat) (unique : axes.Nodup) :
    scatter (scatter base axes first) axes second = scatter base axes second := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have same : bit (scatter (scatter base axes first) axes second) axis = bit (scatter base axes second) axis := by
    by_cases present : axis ∈ axes
    · obtain ⟨index,bound,equal⟩ := List.getElem_of_mem present
      subst axis
      rw [RuntimeScatterTransport.scatter_at _ _ axes unique index bound,
        RuntimeScatterTransport.scatter_at _ _ axes unique index bound]
    · rw [RuntimeScatterTransport.scatter_outside _ _ axis axes present,
        RuntimeScatterTransport.scatter_outside _ _ axis axes present,
        RuntimeScatterTransport.scatter_outside _ _ axis axes present]
  simp only [bit] at same
  rw [← Nat.toNat_testBit _ axis,← Nat.toNat_testBit _ axis] at same
  cases left : (scatter (scatter base axes first) axes second).testBit axis <;>
    cases right : (scatter base axes second).testBit axis <;> simp_all

/-- The spectator coordinate is the complete parent basis label with these
selected axes cleared. Its dependence on the logical input is unrestricted. -/
noncomputable def encodedParent {Reference : Type} (axes : List Nat) (code : Matrix)
    (joint : Nat → Nat → Reference → ℂ) (physical : Nat) (reference : Reference) : ℂ :=
  action code (fun logical (environment : Nat × Reference) => joint logical environment.1 environment.2)
    (gather physical axes) (scatter physical axes 0,reference)

def sourceSlice {Reference : Type} (axes : List Nat) (base : Nat)
    (joint : Nat → Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fun logical reference => joint logical (scatter base axes 0) reference

private theorem encoded_pull {Reference : Type} (axes : List Nat) (unique : axes.Nodup) (code : Matrix)
    (joint : Nat → Nat → Reference → ℂ) (base input : Nat) (reference : Reference)
    (bound : input < 2^axes.length) :
    encodedParent axes code joint (scatter base axes input) reference =
      action code (sourceSlice axes base joint) input reference := by
  unfold encodedParent
  rw [Qleisli.RuntimeFiniteTargetScatter.gather_scatter base input axes unique bound,
    scatter_overwrite base input 0 axes unique]
  rfl

/-- This private bridge substitutes the source CodeSpace equation into the
same literal parent event action, under the real local final reorder. -/
private theorem source_parent_action
    {dependencies program block primitiveStart primitiveCount primitiveInput primitiveOutput role kind
      operations before after localBefore localAfter axes port output form parentEvents childEvents}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block primitiveStart primitiveCount
      primitiveInput primitiveOutput role kind)
    (binding : RuntimePrimitiveSource.Checked primitive)
    (facts : Facts dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents)
    (unique : axes.Nodup) (axisLength : axes.length = port.wires.length)
    (sameFragment : RuntimePureInterval.fragment primitive.interval.selected primitive.interval.operations [primitiveOutput] =
      RuntimePureInterval.fragment [port] operations [output]) :
    ((RuntimeSourcePrimitiveAction.operand binding.event).bind
      (fun (op,owner) => Semantics.PrimitiveOperator.meaning op owner.basis)) = some primitive.expected ∧
    ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base row : Nat) (reference : Reference),
      row < primitive.physical.rows →
      Qleisli.Semantics.RawAction.event dependencies
        (.reorder port.wires.length (port.wires.map port.wires.idxOf))
        (fun value => Qleisli.Semantics.RawAction.events dependencies parentEvents
          (fun input => encodedParent axes primitive.inputCode joint input reference) (scatter base axes value)) row =
      action primitive.outputCode
        (fun logical ref => action primitive.expected (sourceSlice axes base joint) logical ref) row reference := by
  have source := RuntimeSourcePrimitiveAction.reference_action primitive binding
  have read := primitive.physicalRead
  rw [sameFragment] at read
  obtain ⟨receipts⟩ := reconstruction_receipts dependencies (RuntimePureInterval.fragment [port] operations [output])
    primitive.physical port.wires.length form.tape (port.wires.map port.wires.idxOf) _
    (fragment_trace facts) rfl rfl read
  obtain ⟨_physicalRows,_physicalCols,valid,physicalAction⟩ :=
    reconstruction_action dependencies port.wires.length form.tape (port.wires.map port.wires.idxOf) primitive.physical receipts
  refine ⟨source.2.1,?_⟩
  intro Reference joint base row reference bound
  let physicalInput := fun input ref => action primitive.inputCode (sourceSlice axes base joint) input ref
  have parentSlice : (fun value => Qleisli.Semantics.RawAction.events dependencies parentEvents
        (fun input => encodedParent axes primitive.inputCode joint input reference) (scatter base axes value)) =
      Qleisli.Semantics.RawAction.circuit dependencies form.tape
        (fun input => encodedParent axes primitive.inputCode joint (scatter base axes input) reference) := by
    funext value
    have actual := facts.action (encodedParent axes primitive.inputCode joint) reference base value
    rw [facts.childCircuit] at actual
    exact actual
  rw [parentSlice]
  calc
    _ = Qleisli.Semantics.RawAction.event dependencies
        (.reorder port.wires.length (port.wires.map port.wires.idxOf))
        (Qleisli.Semantics.RawAction.circuit dependencies form.tape (fun input => physicalInput input reference)) row := by
      change ((List.range (2^port.wires.length)).map (fun input =>
        if gather input (port.wires.map port.wires.idxOf) == row then _ else 0)).sum = _
      apply Qleisli.Exact.sum_map_congr
      intro input member
      have inside := List.mem_range.mp member
      have same := Qleisli.Finite.rawCircuit_congr dependencies port.wires.length form.tape _ _ valid
        (fun label small => encoded_pull axes unique primitive.inputCode joint base label reference
          (by simpa only [axisLength] using small)) input inside
      rw [same]
    _ = action primitive.physical physicalInput row reference :=
      (physicalAction physicalInput row reference bound).symm
    _ = _ := source.2.2 (sourceSlice axes base joint) row reference bound

/-- The original source operator acts through these exact parent events and
the explicit local reorder. This is a proposition about the actual call, not
an additional native acceptance judgment. -/
def MixedAction {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (portBinding : RuntimeOwnerMap.Binding) (form : Form) (output : Nat)
    {primitiveStart primitiveCount primitiveInput primitiveOutput role kind}
    (primitive : RuntimePrimitiveAction.Checked scope.prepared.block primitiveStart primitiveCount primitiveInput primitiveOutput role kind)
    (binding : RuntimePrimitiveSource.Checked primitive) : Prop :=
    ∃ parentEvents childEvents,
      Facts dependencies [form.operation portBinding.port.token output]
        scope.interval.before.quantum scope.interval.after.quantum scope.localEntry.quantum scope.localAfter.quantum
        (RuntimeNamedFrameAxes.mixedAxes scope) portBinding.port output form parentEvents childEvents ∧
      ((RuntimeSourcePrimitiveAction.operand binding.event).bind
        (fun (op,owner) => Semantics.PrimitiveOperator.meaning op owner.basis)) = some primitive.expected ∧
      ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base row : Nat) (reference : Reference),
        row < primitive.physical.rows →
        Qleisli.Semantics.RawAction.event dependencies
          (.reorder portBinding.port.wires.length (portBinding.port.wires.map portBinding.port.wires.idxOf))
          (fun value => Qleisli.Semantics.RawAction.events dependencies parentEvents
            (fun input => encodedParent (RuntimeNamedFrameAxes.mixedAxes scope) primitive.inputCode joint input reference)
            (scatter base (RuntimeNamedFrameAxes.mixedAxes scope) value)) row =
        action primitive.outputCode
          (fun logical ref => action primitive.expected
            (sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base joint) logical ref) row reference

/-- The original primitive is indexed by this SAME mixed scope's actual
prepared block. Exact fragment equality binds its complete selected ports,
literal operations and output to the named call. The resulting single equation
connects the original source operator to the real parent Raw events, including
the local final reorder, on every correlated spectator/reference fibre. -/
theorem mixed_reference_action
    {dependencies program block start count inputs ordinary effect sources caller before child retired childValue}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired childValue)
    (portBinding : RuntimeOwnerMap.Binding) (oneInput : boundary.input.ordered = [portBinding])
    (form : Form) (output : Nat)
    (literal : (block.operations.drop start).take count =
      [Semantics.Observation.Op.pure (form.operation portBinding.port.token output)])
    {primitiveStart primitiveCount primitiveInput primitiveOutput role kind}
    (primitive : RuntimePrimitiveAction.Checked scope.prepared.block primitiveStart primitiveCount primitiveInput primitiveOutput role kind)
    (binding : RuntimePrimitiveSource.Checked primitive)
    (sameFragment : RuntimePureInterval.fragment primitive.interval.selected primitive.interval.operations [primitiveOutput] =
      RuntimePureInterval.fragment [portBinding.port] [form.operation portBinding.port.token output] [output]) :
    MixedAction scope portBinding form output primitive binding := by
  obtain ⟨parentEvents,childEvents,facts⟩ := mixed_single_owner_lift scope boundary portBinding oneInput form output literal
  have selected : scope.selected = [portBinding.port] := by
    rw [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary,oneInput]
    rfl
  have length : (RuntimeNamedFrameAxes.mixedAxes scope).length = portBinding.port.wires.length := by
    simp [RuntimeNamedFrameAxes.mixedAxes,RuntimeForestCode.portAxes,selected]
  exact ⟨parentEvents,childEvents,facts,
    source_parent_action primitive binding facts (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1 length sameFragment⟩

#print axioms mixed_reference_action

end Qleisli.RuntimeNamedPrimitiveSourceLift
