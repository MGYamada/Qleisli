import Qleisli.RuntimeSelectionGraphHistory
import Qleisli.RuntimePureProviderLogicalAction

/-! The original coherent selection's literal Raw action agrees with its
written arm graph evaluations in the same complete caller history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionGraphAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open Semantics.Exact (Matrix)
open RuntimeSelectionSteps (Edge)
open RuntimeSemanticForest (Frame ownerLayout owner_layout)
open RuntimeGraphCoefficients (Coefficient)
open RuntimeForestRegroup (sourceDimension)
open Qleisli.Semantics.RawAction (events)
open Qleisli.Semantics.ObservingAction (run)
open Semantics.Observation (readOps)
open RuntimePureBody (Node)
open RuntimeLiteralBody
open RuntimeNamedSourceFlow (Aligned)
open RuntimeNamedChildRuns (OrdinaryAligned)

/-- At each selector ordinal, link the actual written arm's action to the
parent's independently evaluated Raw sector on arbitrary reference columns. -/
theorem written_arm_sector_action {sources owner name offset selectorBasis targetBasis Arm written armOrdinal}
    (source : QuantumArms.TableWith sources owner name offset selectorBasis targetBasis Arm written armOrdinal)
    (produced : Fin source.arms.length → Matrix → Prop)
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {labels : List Nat} {arms logical : List Matrix}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels arms) logical)
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (origin : RuntimeSelectionLogicalRead.FromArms source produced
      (.selection frame selectorBits targetBits retained restricted inputCode outputCode labels arms logical equations codes layouts))
    (ordinal : Fin labels.length) :
    ∃ index matrix, armOrdinal source.arms[index] = ordinal.val ∧ produced index matrix ∧
      ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (row : Nat) (ref : Reference), row < outputCode.rows →
        let label := labels[ordinal.val]
        let action := Qleisli.Semantics.Exact.action
        Qleisli.Semantics.RawAction.circuit dependencies retained.steps
            (fun coordinate => Qleisli.NominalSector.encodedTargets selectorBits inputCode joint coordinate ref)
            (FiniteRestriction.pack selectorBits label row) =
          action outputCode (fun output reference => action matrix (joint label) output reference) row ref := by
  have length := congrArg List.length origin.2.2.1
  obtain ⟨index,matrix,written,found,fromArm⟩ := origin.at_ordinal ⟨ordinal.val,length ▸ ordinal.isLt⟩
  obtain ⟨_,table⟩ := RuntimeMultiwayGram.ordinal_table equations
  have requested : arms[ordinal.val]? = some (table.arm ordinal) := List.getElem?_eq_getElem (table.count.symm ▸ ordinal.isLt)
  have actionEq := Option.some.inj (requested.symm.trans found)
  obtain ⟨work,left,read⟩ := restricted
  have literal := Raw.Sector.read_bound _ _ _ _ _ work left read
  refine ⟨index,matrix,written,fromArm,?_⟩
  intro Reference joint row ref bounded
  simpa only [actionEq] using
    Qleisli.NominalSector.read_logical_sector_action literal (table.arm_checked ordinal) joint row ref bounded

private theorem target_shapes
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {labels : List Nat} {arms : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (table : RuntimeMultiwayGram.OrdinalTable inputCode outputCode retained.sectors labels arms)
    (after : Frame codes.owners.transport.after.bindings) :
    let all := codes.owners.transport.after.bindings
    let returned := codes.owners.returned.second
    ∀ matrix ∈ arms, matrix.rows = sourceDimension all returned ∧ matrix.cols = sourceDimension all returned := by
  intro all returned matrix member
  have source := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have present : returned ∈ all := source.1 (by simp [returned])
  have sameOwners : codes.owners.returned.first.owner = selector ∧ returned.owner = target := by
    simpa only [returned,List.map_cons,List.map_nil,List.cons.injEq,and_true] using source.2
  have original := (owner_layout (after.available returned present)).1
  have targetRead : Semantics.FiniteCarrier.layout target.basis = some (ownerLayout returned) := by
    rw [← sameOwners.2]
    exact original
  obtain ⟨layout,layoutRead,_,inputEq,outputEq,_,_⟩ := RuntimeFiniteTargetCode.target_codes frame codes layouts
  have equal := Option.some.inj (layoutRead.symm.trans targetRead)
  have cardinal : sourceDimension all returned = layout.labels.length := by
    simp only [sourceDimension,if_pos present,Semantics.FiniteCarrier.dimension,original,Option.map_some,
      Option.getD_some,← equal]
  obtain ⟨index,inside,atIndex⟩ := List.getElem_of_mem member
  let ordinal : Fin labels.length := ⟨index,table.count ▸ inside⟩
  have actual : table.arm ordinal = matrix := atIndex
  have equation := table.arm_checked ordinal
  rw [actual] at equation
  exact ⟨equation.2.2.1.trans ((congrArg Matrix.cols outputEq).trans cardinal.symm),
    equation.2.1.trans ((congrArg Matrix.cols inputEq).trans cardinal.symm)⟩

/-- Direct selection runs the independently evaluated written arm graphs on
the same complete owner/reference state, not just the retained arm matrices. -/
theorem planned_selection_action {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge)
    {program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked root.dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read root.dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {labels : List Nat} {arms logical : List Matrix}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels arms) logical)
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (original : RuntimeNamedChildRuns.SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root)
      (.selection frame selectorBits targetBits retained restricted inputCode outputCode labels arms logical equations codes layouts))
    (before : Frame codes.owners.before.bindings) :
    ∃ coefficients : List Coefficient, List.Forall₂ RuntimeSelectionGraphHistory.Coefficients arms coefficients ∧
      ∃ trace : RuntimeSelectionTraceEvidence.TraceEvidence frame codes.owners selectorBits targetBits retained restricted,
      ∃ after : Frame codes.owners.transport.after.bindings,
        ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference),
          events root.dependencies trace.traceResult.events
            (fun input => RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint input reference)
            physical =
          RuntimeSemanticForest.action after frame.interval.after.quantum.frame
            (RuntimeSelectionGraphHistory.sourceAction codes.owners.transport.after.bindings
              codes.owners.returned.first codes.owners.returned.second coefficients joint) physical reference := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,evaluated⟩ :=
    RuntimeSelectionGraphSource.planned_selection_sources catalogue root scope original
  obtain ⟨coefficients,related⟩ := RuntimeSelectionGraphHistory.table_coefficients evaluated.2.2.2
  obtain ⟨_,table⟩ := RuntimeMultiwayGram.ordinal_table equations
  obtain ⟨trace,after,literal⟩ := RuntimeSemanticSelectionSource.direct_selection_action
    frame restricted codes layouts table before
  have source := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := source.1 (by simp)
  refine ⟨coefficients,related,trace,after,?_⟩
  intro Reference joint physical reference
  rw [RuntimeSelectionGraphHistory.source_action_eq after _ _ member related
    (target_shapes frame codes layouts table after) joint]
  exact literal joint physical reference

def CoefficientsFor {artifact : Artifact} {catalogue : GenericCatalogue.Checked artifact.sources}
    {root : Validity.Root} (scope : List Edge)
    {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    {program block} (node : Node root.dependencies program block) (coefficients : List Coefficient) : Prop :=
  match node with
  | .selection (selector := actualSelector) (target := actualTarget) _ _ _ _ _ _ _ labels arms .. =>
    actualSelector.basis = selector ∧ actualTarget.basis = target ∧ labels = table.layout.labels ∧
    RuntimeSelectionGraphHistory.OrderedCoefficients catalogue root scope table
      (List.range table.layout.labels.length) arms coefficients
  | _ => False

def OriginalCoefficients {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {program block}
    (node : Node root.dependencies program block) (coefficients : List Coefficient) : Prop :=
  ∃ (owner name : String) (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (offset : Nat) (selector target : Semantics.FiniteCarrier.Basis)
    (naturals : PhaseApplication.Naturals artifact.sources) (writtenScope : List String)
    (table : QuantumArms.Table artifact.sources owner name offset selector target),
    RuntimeInterval.Computed (QuantumArms.readArmsWithInstantiation source.signature.original
      source.signature.instantiation source.signature.supply offset selector target (some naturals) writtenScope) table ∧
    CoefficientsFor (catalogue := catalogue) (root := root) scope table node coefficients

/-- The coefficient at each selector ordinal comes from the fold over that
written arm's actual staged graph records. -/
theorem original_coefficients {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {program block}
    {node : Node root.dependencies program block}
    (original : RuntimeNamedChildRuns.SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node) :
    ∃ coefficients, OriginalCoefficients catalogue root scope node coefficients := by
  obtain ⟨owner,name,source,offset,selector,target,naturals,writtenScope,table,read,evaluated⟩ :=
    RuntimeSelectionGraphSource.planned_selection_sources catalogue root scope original
  cases node
  case selection =>
    obtain ⟨coefficients,ordered⟩ := RuntimeSelectionGraphHistory.ordered_coefficients evaluated.2.2.2
    exact ⟨coefficients,owner,name,source,offset,selector,target,naturals,writtenScope,table,read,evaluated.1,evaluated.2.1,evaluated.2.2.1,ordered⟩
  all_goals exact False.elim evaluated

noncomputable def sourceGraphSelection {dependencies program block}
    (node : Node dependencies program block) (coefficients : List Coefficient)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match node with
  | .selection _ _ _ _ _ _ _ _ _ _ _ codes _ =>
    some [{source with
      owners := {source.owners with bindings := codes.owners.transport.after.bindings}
      operator := RuntimeSelectionGraphHistory.sourceAction codes.owners.transport.after.bindings
        codes.owners.returned.first codes.owners.returned.second coefficients source.operator}]
  | _ => none

theorem selection_history_with {root : Validity.Root}
    {program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked root.dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read root.dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {labels : List Nat} {arms logical : List Matrix}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels arms) logical)
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels) :
    let node := Node.selection frame selectorBits targetBits retained restricted inputCode outputCode labels
      arms logical equations codes layouts
    ∀ {coefficients : List Coefficient}, List.Forall₂ RuntimeSelectionGraphHistory.Coefficients arms coefficients →
    ∀ (ordinaryInputs : List Nat) (inherited : Option (Nat → Prop))
      {ownerBefore ownerAfter ordinaryBefore ordinaryAfter},
      Aligned ownerBefore ownerAfter (.pure node) →
      OrdinaryAligned ordinaryBefore ordinaryAfter (.pure node) →
      ∀ {chunk source history results},
      readOps block.fuel (nodeSpan node).checked.before.quantum.reference (nodeSpan node).operations =
        some ((nodeSpan node).checked.after.quantum.reference,chunk) →
      SemanticHistoryAgreesWithInherited inherited ordinaryInputs (nodeSpan node).checked.before
        ownerBefore ordinaryBefore source history →
      run root.dependencies block.fuel chunk history = some results →
      ∃ expected, sourceGraphSelection node coefficients source = some expected ∧
        List.Forall₂ (SemanticHistoryAgreesWithInherited inherited ordinaryInputs (nodeSpan node).checked.after
          ownerAfter ordinaryAfter) expected results := by
  intro node coefficients related ordinaryInputs inherited ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk source history results read agrees executed
  have beforeMap : ownerBefore.bindings = codes.owners.before.bindings := owners.1
  obtain ⟨_,_,_,input,_⟩ := agrees.2.2.2.2
  let entry : Frame codes.owners.before.bindings := beforeMap ▸ input
  obtain ⟨_,table⟩ := RuntimeMultiwayGram.ordinal_table equations
  obtain ⟨_,after,_⟩ := RuntimeSemanticSelectionSource.direct_selection_action frame restricted codes layouts table entry
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have operator := RuntimeSelectionGraphHistory.source_action_eq after
    codes.owners.returned.first codes.owners.returned.second member related
    (target_shapes frame codes layouts table after) source.operator
  obtain ⟨expected,evaluated,paired⟩ := semantic_direct_selection_refines frame restricted equations codes layouts
    ordinaryInputs inherited owners ordinary read agrees executed
  refine ⟨expected,?_,paired⟩
  change sourceDirectSelection node source = some expected at evaluated
  simpa only [node,sourceGraphSelection,sourceDirectSelection,operator] using evaluated

/-- The selected arm graphs can supply the operator of the same ordered
history that carries the original SSA values and inherited measurements. -/
theorem planned_selection_history {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge)
    {program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked root.dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read root.dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {labels : List Nat} {arms logical : List Matrix}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels arms) logical)
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels) :
    let node := Node.selection frame selectorBits targetBits retained restricted inputCode outputCode labels
      arms logical equations codes layouts
    RuntimeNamedChildRuns.SelectionOrigin (RuntimeSelectionGraphSource.execution artifact catalogue root) node →
    ∀ (ordinaryInputs : List Nat) (inherited : Option (Nat → Prop))
      {ownerBefore ownerAfter ordinaryBefore ordinaryAfter},
      Aligned ownerBefore ownerAfter (.pure node) →
      OrdinaryAligned ordinaryBefore ordinaryAfter (.pure node) →
      ∀ {chunk source history results},
      readOps block.fuel (nodeSpan node).checked.before.quantum.reference (nodeSpan node).operations =
        some ((nodeSpan node).checked.after.quantum.reference,chunk) →
      SemanticHistoryAgreesWithInherited inherited ordinaryInputs (nodeSpan node).checked.before
        ownerBefore ordinaryBefore source history →
      run root.dependencies block.fuel chunk history = some results →
      ∃ coefficients expected, List.Forall₂ RuntimeSelectionGraphHistory.Coefficients arms coefficients ∧
        sourceGraphSelection node coefficients source = some expected ∧
        List.Forall₂ (SemanticHistoryAgreesWithInherited inherited ordinaryInputs (nodeSpan node).checked.after
          ownerAfter ordinaryAfter) expected results := by
  intro node original ordinaryInputs inherited ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk source history results read agrees executed
  obtain ⟨coefficients,owner,name,written,offset,selectorBasis,targetBasis,naturals,writtenScope,table,sourceRead,ordered⟩ :=
    original_coefficients catalogue root scope original
  obtain ⟨expected,evaluated,paired⟩ := selection_history_with frame restricted equations codes layouts
    ordered.2.2.2.1 ordinaryInputs inherited owners ordinary read agrees executed
  exact ⟨coefficients,expected,ordered.2.2.2.1,evaluated,paired⟩

#print axioms original_coefficients
#print axioms written_arm_sector_action
#print axioms planned_selection_history
#print axioms planned_selection_action
end Qleisli.RuntimeSelectionGraphAction

namespace Qleisli.RuntimeInlineArmBoundary
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open Semantics.Observation (readOps)
open Semantics.Exact (Matrix)
open Semantics.FiniteCarrier (Layout layout encoding)
open Qleisli.Semantics.Exact (action)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.Semantics.RawAction (event)
open RuntimeNamedThreePackedOutput (readerFinish final_axes final_axes_permutation)
open RuntimeNamedThreePackedInstrument (pureHistory run_pure)
open RuntimePureProviderBoundary (packedAction packed_code_action reorder_packed)
open RuntimeSemanticForest (Frame product)

/-- The prepared full block and the mathematical reader enumerate the same
pure prefix, with exactly the reader's final output permutation. -/
theorem prepared_pure_trace {dependencies program}
    (prepared : RuntimeInterval.Prepared dependencies program)
    (closed : program.classicalInputs = [])
    (shape : Qleisli.RuntimePureNamedScope.PureBlock prepared.block)
    (last : RuntimeInterval.Checked prepared.block prepared.block.operations.length 0) :
    let block := prepared.block
    let finish := readerFinish program last.before.quantum.reference
    ∃ rawEvents : List Semantics.Raw.Event,
      readOps block.fuel block.entry.quantum.reference block.operations =
        some (last.before.quantum.reference,rawEvents.map Semantics.Observation.Event.pure) ∧
      Semantics.Observation.read program = some prepared.whole.prepared ∧
      prepared.whole.prepared.events = (rawEvents ++ [finish]).map Semantics.Observation.Event.pure ∧
      prepared.whole.prepared.state = last.before.quantum.reference := by
  intro block finish
  obtain ⟨_,operations,pureOps⟩ := shape
  obtain ⟨work,left,checkedPrefix⟩ := last.prefixRead
  have runOps := congrArg (fun ops => (Raw.Observation.checkOps dependencies block.fuel
    block.entry ops).run work) pureOps
  have purePrefix := runOps.symm.trans (by simpa only [List.take_length] using checkedPrefix)
  obtain ⟨rawEvents,traced⟩ :=
    RuntimeIntervalTrace.checkOps_pure_trace dependencies block.fuel block.entry last.before operations work left
      purePrefix
  have literal : readOps block.fuel block.entry.quantum.reference block.operations =
      some (last.before.quantum.reference,rawEvents.map Semantics.Observation.Event.pure) := by
    exact (congrArg (readOps block.fuel block.entry.quantum.reference) pureOps).trans
      (RuntimeAdjacentSlices.readOps_pure 64 _ _ _ traced)
  have original := prepared.originalRoot.reader
  have entry := RuntimePureProviderExecution.entry_reference prepared closed
  have whole : Semantics.Observation.read program =
      some ⟨last.before.quantum.reference,(rawEvents ++ [finish]).map Semantics.Observation.Event.pure,
        (Semantics.RawTrace.initial program.inputs).frame.length⟩ := by
    unfold Semantics.Observation.read
    have read := literal
    change readOps 65 block.entry.quantum.reference program.operations = _ at read
    rw [show block.entry.quantum.reference = Semantics.RawTrace.initial program.inputs from entry] at read
    simp only [read,bind,Option.bind,pure,List.map_append,List.map_cons,List.map_nil,finish,readerFinish]
  have same := Option.some.inj (original.symm.trans whole)
  exact ⟨rawEvents,literal,original,congrArg Semantics.Observation.Prepared.events same,
    congrArg Semantics.Observation.Prepared.state same⟩

/-- Apply the actual Raw reconstruction and map equation to the prefix history
and its literal final permutation. -/
theorem prepared_pure_execution {dependencies program inputCode outputCode actual}
    (prepared : RuntimeInterval.Prepared dependencies program)
    (closed : program.classicalInputs = [])
    (shape : Qleisli.RuntimePureNamedScope.PureBlock prepared.block)
    (last : RuntimeInterval.Checked prepared.block prepared.block.operations.length 0)
    (actualRead : RuntimeInterval.Computed (Raw.BranchFunction.reconstruct dependencies program) actual)
    (code : QleisliKernel.CodeSpace.Map inputCode outputCode actual)
    (joint : Nat → Nat → ℂ) :
    let block := prepared.block
    let initial : History := ⟨[],[],action inputCode joint⟩
    let finish := readerFinish program last.before.quantum.reference
    ∃ final : History,
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run dependencies block.fuel events initial) = some [final] ∧
      ∀ row column, row < actual.rows →
        event dependencies finish (fun i => final.operator i column) row =
          action outputCode (fun i ref => action code.logical joint i ref) row column := by
  intro block initial finish
  obtain ⟨rawEvents,literal,original,pureEvents,_⟩ := prepared_pure_trace prepared closed shape last
  let final := pureHistory dependencies rawEvents initial
  refine ⟨final,?_,?_⟩
  · rw [literal]
    exact run_pure dependencies 64 rawEvents initial
  · intro row column bound
    obtain ⟨work,left,matrix⟩ := actualRead
    have physical := Qleisli.Raw.PureInstrumentAction.reconstructed_action dependencies
      program actual work left matrix prepared.whole.prepared original
      (rawEvents ++ [finish]) pureEvents (action inputCode joint) row column bound
    rw [Qleisli.RawActionComposition.events_append] at physical
    exact physical.symm.trans (Qleisli.CodeSpace.map_reference_action code joint row column bound)

/-- A singleton checked source role is encoded through the actual closed Raw
entry port in its original wire order. -/
theorem singleton_input_agreement {dependencies program inputCode}
    (prepared : RuntimeInterval.Prepared dependencies program)
    (closed : program.classicalInputs = [])
    (target : RuntimeOwnerMap.Owner) (port : Semantics.Raw.Port)
    (rawInputs : program.inputs = [port])
    (source : RuntimeStructuralAction.SourceState)
    (assigned : source.bindings = [⟨target,port⟩])
    (inputCodeRead : RuntimeInterval.Computed (Carrier.ownerCode [⟨port,target.basis⟩]) inputCode)
    (input : RuntimeOwnerMap.Checked [target] prepared.block.entry)
    (reordered : RuntimeInterval.Computed
      (RuntimePureBody.reordered [target] prepared.block.entry source.bindings) input)
    (inputs : List Nat) (joint : Nat → Nat → ℂ) :
    let sourceInitial : Qleisli.RuntimeLiteralBody.SourceHistory := ⟨source,[],[],joint,[]⟩
    let initial : History := ⟨[],[],action inputCode joint⟩
    Qleisli.RuntimeCallHistory.SourceAgreementWithin (some (· = {})) none inputs prepared.block.entry
      {source with bindings := input.bindings} {} sourceInitial initial := by
  intro sourceInitial initial
  let state := prepared.block.entry
  have original := RuntimePureProviderExecution.entry_reference prepared closed
  have nativeFrame : state.quantum.reference = ⟨[port],port.wires⟩ :=
    original.trans (by simp [rawInputs,Semantics.RawTrace.initial])
  have wires : state.quantum.frame = port.wires := congrArg Semantics.RawTrace.Interface.frame nativeFrame
  have same : input.bindings = source.bindings := by
    have lookup := Qleisli.RuntimeLiteralHistory.reordered_source input reordered
    rw [assigned] at lookup ⊢
    have exactOrder : [target].mapM (RuntimeOwnerMap.byOwner [⟨target,port⟩]) = some [⟨target,port⟩] := by
      simp [RuntimeOwnerMap.byOwner]
    exact Option.some.inj (lookup.symm.trans exactOrder)
  have actualBindings : input.bindings = [⟨target,port⟩] := same.trans assigned
  have codeRead : RuntimeInterval.Computed (Carrier.ownerCode (RuntimeForestCode.carrierOwners input.bindings))
      inputCode := by
    rw [actualBindings]
    exact inputCodeRead
  obtain ⟨available,codeEq⟩ := RuntimeSparseOperationAction.original_block_code codeRead
  obtain ⟨frame⟩ := RuntimeSemanticForest.frame_exists available
  have valid : Raw.stateValid state.quantum = true := Raw.inputs_valid _ _ _ rfl (by
    obtain ⟨work,left,ran⟩ := prepared.inputRead
    unfold PureInterval.initial at ran
    obtain ⟨quantum,_,inserted,returned⟩ := bind_success _ _ _ _ _ ran
    rw [closed,List.foldlM_nil] at returned
    have finish := congrArg Raw.Observation.State.quantum (pure_success _ _ _ _ returned).1
    change state.quantum = quantum at finish
    rw [finish]
    exact (lift_success _ _ _ _ inserted).1)
  have allWires : input.bindings.flatMap (fun b => b.port.wires) = state.quantum.frame := by
    simp [actualBindings,wires]
  have width : (product input.bindings).bits = state.quantum.frame.length :=
    (RuntimeSparseBlockEncoding.product_width available).trans (congrArg List.length allWires)
  have axes : RuntimeForestCode.forestAxes state.quantum.frame input.bindings = List.range state.quantum.frame.length := by
    unfold RuntimeForestCode.forestAxes
    rw [allWires]
    exact RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ valid).frame
  refine ⟨rfl,?_,?_⟩
  · change sourceInitial.owners = {source with bindings := input.bindings}
    rw [same]
  · change initial.hidden = sourceInitial.outcomes.map Prod.snd ∧
      Qleisli.RuntimeLiteralBranchChoice.measurementBits [] initial.values = some sourceInitial.measurements ∧ _
    refine ⟨rfl,rfl,⟨RuntimeOrdinarySSA.Agreement.empty _ _,fun id member => by cases member⟩,
      _,input,rfl,frame,?_⟩
    intro col row bounded
    have codeBound : row < inputCode.rows := by
      rw [codeEq]
      change row < 2^(product input.bindings).bits
      rwa [width]
    have packed := packed_code_action frame codeEq joint row col codeBound
    change action inputCode joint row col =
      RuntimeSemanticForest.action frame state.quantum.frame joint row col
    rw [← packed]
    unfold packedAction RuntimeSemanticForest.action RuntimeForestCode.embed
    rw [axes,Raw.Sector.gather_identity row _ bounded]

open RuntimePureBody (InlineChecked Context BlockRunner Step runBlockCore)
open QleisliKernel.SourceTypes

theorem inline_input_agreement {artifact root execution rootOwner rootName owner name}
    {site : SourceRuntimeContext.SelectionEvent artifact.sources owner} {index : Nat}
    {sameName : site.callerName = name} {arm : SourceRuntimeTrace.InlineArmBody site index}
    {replayed : RuntimeInterval.Computed (SourceRuntimeTrace.readInlineArmBody site index) arm}
    {implementation : Nat} {request : Context}
    {plan : execution.queries.BodyData (.coherentArm sameName arm replayed) request}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    {parent : RuntimeStructuralAction.SourceState} {runArm : BlockRunner artifact root execution}
    (checked : InlineChecked sameName arm replayed implementation request plan path parent runArm)
    (inputs : List Nat) (joint : Nat → Nat → ℂ)
    (input : RuntimeOwnerMap.Checked [site.target] checked.forward.prepared.block.entry)
    (reordered : RuntimeInterval.Computed
      (RuntimePureBody.reordered [site.target] checked.forward.prepared.block.entry
        (checked.forward.initial parent).bindings) input) :
    let source := checked.forward.initial parent
    let sourceInitial : Qleisli.RuntimeLiteralBody.SourceHistory := ⟨source,[],[],joint,[]⟩
    let initial : History := ⟨[],[],action checked.action.inputCode joint⟩
    Qleisli.RuntimeCallHistory.SourceAgreementWithin (some (· = {})) none inputs checked.forward.prepared.block.entry
      {source with bindings := input.bindings} {} sourceInitial initial := by
  have preflight := checked.forward.preflight
  simp only [Raw.BranchFunction.preflight,Bool.and_eq_true,List.isEmpty_iff] at preflight
  exact singleton_input_agreement checked.forward.prepared preflight.1.1.1.2 site.target checked.forward.input
    checked.forward.inputOrder (checked.forward.initial parent) rfl checked.action.inputRead input reordered inputs joint

/-- The verified complete owner map and exact declared return tokens determine
the Raw reader's final permutation, including empty-width owner ports. -/
theorem packed_return_agreement {dependencies program roles state bindings}
    (physical : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true)
    (tokens : program.outputs = physical.bindings.map (fun binding => binding.port.token))
    (same : physical.bindings = bindings)
    (output : Frame bindings) (source native : Nat → Nat → ℂ)
    (encoded : ∀ col row, row < 2^state.quantum.frame.length →
      native row col = RuntimeSemanticForest.action output state.quantum.frame source row col) :
    ∀ row col, row < 2^state.quantum.frame.length →
      event dependencies (readerFinish program state.quantum.reference) (fun i => native i col) row =
        packedAction output source row col := by
  subst bindings
  have finish : readerFinish program state.quantum.reference =
      .reorder state.quantum.frame.length (RuntimeForestCode.forestAxes state.quantum.frame physical.bindings) := by
    unfold readerFinish
    rw [tokens]
    exact congrArg (Semantics.Raw.Event.reorder state.quantum.frame.length) (final_axes physical valid)
  intro row col bound
  rw [finish]
  obtain ⟨original,inside,coordinate,applied⟩ := RuntimeNamedThreePackedOutput.reorder_gather dependencies _ _
    (final_axes_permutation physical valid) (fun i => native i col) row bound
  rw [applied,encoded col original inside]
  unfold RuntimeSemanticForest.action RuntimeForestCode.embed packedAction
  rw [coordinate]

theorem output_rows {roles state}
    (physical : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true)
    {inputCode outputCode actual : Matrix}
    (map : QleisliKernel.CodeSpace.Map inputCode outputCode actual)
    (read : RuntimeInterval.Computed (Carrier.ownerCode (RuntimeForestCode.carrierOwners physical.bindings)) outputCode) :
    actual.rows = 2^state.quantum.frame.length := by
  obtain ⟨available,code⟩ := RuntimeSparseOperationAction.original_block_code read
  have wires := (physical.complete.flatMap_right (fun port => port.wires)).length_eq
  rw [List.flatMap_map] at wires
  have width : (product physical.bindings).bits = state.quantum.frame.length :=
    (RuntimeSparseBlockEncoding.product_width available).trans
      (wires.trans (Raw.Ownership.valid _ valid).count)
  rw [map.physicalShape.2,code]
  change 2^(product physical.bindings).bits = _
  rw [width]

/-- Decode the returned source history through the true singleton output
layout on both sides of its checked packed equality. -/
theorem logical_from_packed {bindings : RuntimeOwnerMap.Map} (frame : Frame bindings)
    {outputCode : Matrix} {basis : Semantics.FiniteCarrier.Basis} {code : Layout}
    (layoutRead : layout basis = some code)
    (outputLayout : outputCode = encoding code)
    (outputProduct : outputCode = encoding (product bindings))
    (source native : Nat → Nat → ℂ)
    (packed : ∀ row col, row < outputCode.rows →
      packedAction frame source row col = action outputCode native row col) :
    ∀ row col, row < code.labels.length → source row col = native row col := by
  intro row col bounded
  let ordinal : Fin code.labels.length := ⟨row,bounded⟩
  have physicalBound : code.labels[ordinal.val] < outputCode.rows := by
    rw [outputLayout]
    exact (RuntimeForestProduct.layout_bounds _ _ layoutRead).2 _ (List.getElem_mem _)
  have same := packed code.labels[ordinal.val] col physicalBound
  rw [packed_code_action frame outputProduct source code.labels[ordinal.val] col physicalBound,
    outputLayout] at same
  rw [RuntimePureProviderLogicalAction.encoding_label layoutRead source ordinal col,
    RuntimePureProviderLogicalAction.encoding_label layoutRead native ordinal col] at same
  exact same

#print axioms prepared_pure_execution
#print axioms inline_input_agreement
#print axioms packed_return_agreement
#print axioms logical_from_packed

open Qleisli.RuntimeLiteralBody
open RuntimeNamedChildRuns (CheckedStepAt)
open Qleisli.RuntimeCallHistory (SourceAgreementWithin)
open RuntimeProviderSourceEntry (basisColumn action_basisColumn)

/-- The original isolated body, evaluated using its written steps and owner
return, agrees with the checked logical action at every logical output row. -/
theorem original_inline_source_operator {artifact root execution rootOwner rootName owner name}
    {event : SourceRuntimeContext.SelectionEvent artifact.sources owner} {index : Nat}
    {sameName : event.callerName = name} {arm : SourceRuntimeTrace.InlineArmBody event index}
    {replayed : RuntimeInterval.Computed (SourceRuntimeTrace.readInlineArmBody event index) arm}
    {implementation : Nat} {request : Context}
    {plan : execution.queries.BodyData (.coherentArm sameName arm replayed) request}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    {parent : RuntimeStructuralAction.SourceState} (depth : Nat)
    (checked : InlineChecked sameName arm replayed implementation request plan path parent
      (runBlockCore artifact root execution (depth+1)))
    (inputs : List Nat) (scope : List RuntimeSelectionSteps.Edge) (leaves : Nat → ScopedSourceSteps root.dependencies)
    (laws : ∀ fuel, fuel ≤ depth → ∀ {program block} (atStep : List RuntimeSelectionSteps.Edge) (steps : List (Step root.dependencies program block)),
      Qleisli.RuntimePureNamedScope.PureBlock block → ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root execution fuel)
          (RuntimeBranchCondition.rootEntries path) step ∧ NeedsPureLeaf step)
        (leaves fuel atStep) (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id)))
    (joint : Nat → Nat → ℂ) :
    let returned := checked.result.history.bindings
    let initial : SourceHistory := ⟨checked.forward.initial parent,[],[],joint,[]⟩
    ∃ history,
      runSourceHistories (pureRecursiveSourceStepsAt leaves depth scope) [] checked.result.steps [initial] =
        some [history] ∧
      ∀ row col, row < checked.action.code.logical.rows →
        (returnHistory returned history).operator row col =
          action checked.action.code.logical joint row col := by
  intro returned initial
  let source := SourceRuntimeScope.Subject.coherentArm sameName arm replayed
  let prepared := checked.forward.prepared
  let result := (checked.result,checked.receipts)
  let start := checked.forward.initial parent
  let next := runBlockCore artifact root execution depth
  have core := checked.traversal
  have shape := RuntimePureProviderNative.replayed_pure_shape next .rootOrder source path request plan
    start {} prepared result core
  obtain ⟨_,_,_,_,⟨last,lastRead,_⟩,_⟩ := RuntimeNamedChildRuns.step_flow_mode
    artifact root execution next .pureBody .rootOrder
    (RuntimeNamedChildRuns.core_pure_preserves_ordinary artifact root execution depth)
    source path checked.forward.program request plan start {} prepared.block result core
  have preflight := checked.forward.preflight
  simp only [Raw.BranchFunction.preflight,Bool.and_eq_true,List.isEmpty_iff] at preflight
  have closed := preflight.1.1.1.2
  obtain ⟨final,performed,matrixAction⟩ := prepared_pure_execution prepared closed shape last
    checked.action.actualRead checked.action.code joint
  let initialNative : History := ⟨[],[],action checked.action.inputCode joint⟩
  obtain ⟨_,exit,exitRead,exitMap,_,returnMap,histories,evaluated,paired⟩ :=
    original_pure_block_refinement execution depth source path plan start prepared.block result core shape
      inputs leaves laws scope initial initialNative [final] performed
      (fun entry read => inline_input_agreement checked inputs joint entry read)
  have count : histories.length = 1 := by
    simpa only [List.length_map,List.length_singleton] using paired.length_eq
  obtain ⟨history,only⟩ := List.length_eq_one_iff.mp count
  rw [only,List.map_singleton] at paired
  cases paired with
  | cons related _ =>
    obtain ⟨_,_,_,_,_,_,physical,bindings,output,encoded⟩ := related
    have atReturn : exitMap.bindings = returned := congrArg (·.bindings) returnMap |>.symm
    have tokens : checked.forward.program.outputs = physical.bindings.map (·.port.token) := by
      rw [bindings]
      exact checked.action.rawOutputs.symm
    have outputRead : RuntimeInterval.Computed
        (Carrier.ownerCode (RuntimeForestCode.carrierOwners physical.bindings)) checked.action.outputCode := by
      rw [bindings]
      exact checked.action.outputRead
    have order := checked.action.outputOrder
    have size : returned.length = 1 := by
      simpa only [List.length_map,List.length_singleton] using congrArg List.length order
    obtain ⟨binding,one⟩ := List.length_eq_one_iff.mp size
    change checked.result.history.bindings = [binding] at one
    have boundOwner : binding.owner = arm.output := by
      simpa only [one,List.map_singleton,List.cons.injEq,and_true] using order
    have singleRead : RuntimeInterval.Computed
        (Carrier.ownerCode [⟨binding.port,arm.output.basis⟩]) checked.action.outputCode := by
      have read := checked.action.outputRead
      simpa only [one,RuntimeTransformAction.owners,List.map_singleton,boundOwner] using read
    obtain ⟨layout,layoutRead,codeEq,_,_,_⟩ :=
      RuntimeFiniteTargetCode.owner_code_reference arm.output.basis binding.port checked.action.outputCode singleRead
    have rows : checked.action.code.logical.rows = layout.labels.length := by
      simpa only [codeEq] using checked.action.code.logicalShape.2
    obtain ⟨_,productEq⟩ := RuntimeSparseOperationAction.original_block_code outputRead
    rw [bindings] at productEq
    obtain ⟨_,_,_,_,lastState⟩ := prepared_pure_trace prepared closed shape last
    obtain ⟨_,_,_,_,exitState⟩ := prepared_pure_trace prepared closed shape exit
    have same := (lastState.symm.trans exitState).trans
      (congrArg (fun state : Raw.Observation.State => state.quantum.reference)
        (Qleisli.RuntimeOwnerTransitionAction.empty_state exit).symm)
    have valid := exit.history.2.2.1
    let evaluatedReturn := (returnHistory exitMap.bindings history).operator
    have actualRows := output_rows physical valid checked.action.code outputRead
    have packed : ∀ row col, row < checked.action.outputCode.rows →
        packedAction output evaluatedReturn row col =
          action checked.action.outputCode (fun input ref => action checked.action.code.logical joint input ref) row col := by
      intro row col inside
      have physicalRow : row < checked.action.actual.rows := checked.action.code.physicalShape.2 ▸ inside
      have returnedRow : row < 2^exit.after.quantum.frame.length := actualRows ▸ physicalRow
      have fromRaw := matrixAction row col physicalRow
      rw [same] at fromRaw
      exact (packed_return_agreement (dependencies := root.dependencies) physical valid tokens bindings output evaluatedReturn
        final.operator encoded row col returnedRow).symm.trans fromRaw
    refine ⟨history,only ▸ evaluated,?_⟩
    intro row col inside
    have atOrdinal := logical_from_packed output layoutRead codeEq productEq evaluatedReturn
      (fun input ref => action checked.action.code.logical joint input ref) packed row col (rows ▸ inside)
    simpa only [evaluatedReturn,atReturn] using atOrdinal

#print axioms original_inline_source_operator

/-- Evaluate the written steps on the original input basis columns, then read
the returned source coefficient in its logical owner order. -/
noncomputable def evaluateInline {dependencies program block}
    (initial : RuntimeStructuralAction.SourceState) (steps : List (Step dependencies program block))
    (returned : RuntimeOwnerMap.Map) (evaluate : ScopedSourceSteps dependencies) (scope : List RuntimeSelectionSteps.Edge) :
    RuntimeGraphCoefficients.Coefficient :=
  fun row col =>
    let source : SourceHistory := ⟨initial,[],[],basisColumn,[]⟩
    match runSourceHistories (evaluate scope) [] steps [source] with
    | some [history] => (returnHistory returned history).operator row col
    | _ => 0

theorem inline_source_coefficients {artifact root execution rootOwner rootName owner name}
    {event : SourceRuntimeContext.SelectionEvent artifact.sources owner} {index : Nat}
    {sameName : event.callerName = name} {arm : SourceRuntimeTrace.InlineArmBody event index}
    {replayed : RuntimeInterval.Computed (SourceRuntimeTrace.readInlineArmBody event index) arm}
    {implementation : Nat} {request : Context}
    {plan : execution.queries.BodyData (.coherentArm sameName arm replayed) request}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    {parent : RuntimeStructuralAction.SourceState} (depth : Nat)
    (checked : InlineChecked sameName arm replayed implementation request plan path parent
      (runBlockCore artifact root execution (depth+1)))
    (inputs : List Nat) (scope : List RuntimeSelectionSteps.Edge) (leaves : Nat → ScopedSourceSteps root.dependencies)
    (laws : ∀ fuel, fuel ≤ depth → ∀ {program block} (atStep : List RuntimeSelectionSteps.Edge) (steps : List (Step root.dependencies program block)),
      Qleisli.RuntimePureNamedScope.PureBlock block → ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root execution fuel)
          (RuntimeBranchCondition.rootEntries path) step ∧ NeedsPureLeaf step)
        (leaves fuel atStep) (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id))) :
    RuntimeSelectionGraphHistory.Coefficients checked.action.code.logical
      (evaluateInline (checked.forward.initial parent) checked.result.steps checked.result.history.bindings
        (pureRecursiveSourceStepsAt leaves depth) scope) := by
  obtain ⟨history,executionRead,agrees⟩ :=
    original_inline_source_operator depth checked inputs scope leaves laws basisColumn
  intro row col rowBound colBound
  simp only [evaluateInline,executionRead,agrees row col rowBound,action_basisColumn _ row col colBound]

#print axioms inline_source_coefficients
end Qleisli.RuntimeInlineArmBoundary
