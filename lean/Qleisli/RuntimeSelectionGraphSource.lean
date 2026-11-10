import Qleisli.RuntimeGraphSourceEvaluation
import Qleisli.RuntimeNamedChildRuns

/-! The actual staged graph at a written qmatch arm supplies its source
operator at the original selector ordinal. Neither equal description indices
nor equal matrices identify a different occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionGraphSource
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeSelectionSteps (Edge)
open RuntimeSelectionLogicalRead (FromArms GraphData GraphLogical)
open Qleisli.RuntimeNamedChildRuns (SelectionOrigin)
open RuntimeGraphCoefficients (Agrees Coefficient)

abbrev execution (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) : RuntimePureBody.ExecutionMode artifact root :=
  .planned (RuntimeBodyOperations.preparation artifact catalogue)
    (RuntimeBodyOperations.stagedConsumption artifact catalogue root)

def ArmEvaluatedWith {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) (matrix : Semantics.Exact.Matrix) (source : Coefficient) : Prop :=
  ∃ data : GraphData (execution artifact catalogue root).queries table index,
    match data with
    | ⟨implementations,references,plan⟩ =>
      let operation := (table.arms[index]).operation
      let request : RuntimeGraphOperation.Request artifact :=
        ⟨_,_,operation.graph,OperationAccess.controllable,implementations,references,.arm operation⟩
      let continuation := RuntimeBodyOperations.stagedConsumption artifact catalogue root
      ∃ evidence : continuation.Evidence request plan.evidence,
        RuntimeInterval.Computed (continuation.read request plan.evidence) evidence ∧
        matrix = evidence.checked.action ∧
        evidence.checked.outcome.records.foldlM (RuntimeGraphSourceEvaluation.advance scope) [] = some [source] ∧
        Agrees evidence.checked.value source

def ArmEvaluated {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) (matrix : Semantics.Exact.Matrix) : Prop :=
  ∃ source, ArmEvaluatedWith catalogue root scope table index matrix source

theorem arm_evaluated {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) (matrix : Semantics.Exact.Matrix)
    (original : ∃ data, GraphLogical (execution artifact catalogue root) table index data matrix) :
    ArmEvaluated catalogue root scope table index matrix := by
  obtain ⟨⟨implementations,references,plan⟩,original⟩ := original
  obtain ⟨evidence,read,same⟩ := original
  obtain ⟨source,ran,related⟩ := RuntimeGraphSourceEvaluation.checked_graph evidence.checked scope
  exact ⟨source,⟨implementations,references,plan⟩,evidence,read,same,ran,related⟩

/-- The literal selection's original arm table is related in selector order
to the independently evaluated source graphs, using the same planned reader. -/
theorem planned_selection_sources {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {program block} {node : RuntimePureBody.Node root.dependencies program block}
    (original : SelectionOrigin (execution artifact catalogue root) node) :
    ∃ (owner name : String) (source : SourceRuntimeScope.Subject artifact.sources owner name)
      (offset : Nat) (selector target : Semantics.FiniteCarrier.Basis)
      (naturals : PhaseApplication.Naturals artifact.sources) (writtenScope : List String)
      (table : QuantumArms.Table artifact.sources owner name offset selector target),
      RuntimeInterval.Computed (QuantumArms.readArmsWithInstantiation source.signature.original
        source.signature.instantiation source.signature.supply offset selector target (some naturals) writtenScope) table ∧
      FromArms table (ArmEvaluated catalogue root scope table) node := by
  obtain ⟨owner,name,source,offset,selector,target,naturals,writtenScope,table,read,arms⟩ := original
  exact ⟨owner,name,source,offset,selector,target,naturals,writtenScope,table,read,
    arms.weaken (arm_evaluated catalogue root scope table)⟩

#print axioms arm_evaluated
#print axioms planned_selection_sources
end Qleisli.RuntimeSelectionGraphSource
