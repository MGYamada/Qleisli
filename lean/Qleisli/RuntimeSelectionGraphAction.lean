import Qleisli.RuntimeSelectionGraphHistory

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
#print axioms planned_selection_history
#print axioms planned_selection_action
end Qleisli.RuntimeSelectionGraphAction
