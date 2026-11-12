import QleisliKernel.Qirf.RuntimeBodyPlan

/-! Exact source-indexed graph cuts for staged body discovery.
The same original graph supplies occurrence order and every provider count.
Prefix and arm traversals retain their fixed original access demands. These
readers prepare source evidence only; no native action or handle is produced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyPlanReaders
open QleisliKernel Finite SourceTypes
open RuntimeBodyPlan

structure GraphRead {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (demand : StaticOperation.Paths) (before : Queues) (origin : RuntimeGraphOperation.Origin graph := .unlocated) where
  cut : Cut before
  graphPlan : Graph preparation graph demand cut.implementations cut.references origin

def GraphRead.receipt {artifact preparation context description graph demand before origin}
    (read : @GraphRead artifact preparation context description graph demand before origin) :
    RuntimeGraphOperation.PreparedReceipt preparation :=
  ⟨⟨context,description,graph,demand,read.cut.implementations,read.cut.references,origin⟩,
    read.graphPlan.evidence,read.graphPlan.consumed⟩

def readGraph {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (demand : StaticOperation.Paths) (before : Queues) (origin : RuntimeGraphOperation.Origin graph := .unlocated) :
    WorkM (GraphRead preparation graph demand before origin) := do
  let occurrences ← NaturalAffine.witness (StaticOperation.readOccurrences description)
  let count := (RuntimeProviderHeaders.providerIndices description occurrences.val).length
  if enough : count ≤ before.bodies.length then
    match groups : before.references with
    | [] => throw .request
    | references :: remainingReferences =>
      let implementations := before.bodies.take count
      let remainingBodies := before.bodies.drop count
      let cut : Cut before := ⟨implementations,references,remainingBodies,remainingReferences,
        (List.take_append_drop count before.bodies).symm,groups⟩
      let request : RuntimeGraphOperation.Request artifact :=
        ⟨context,description,graph,demand,implementations,references,origin⟩
      let checked ← NaturalAffine.witness (preparation.read request)
      let graphPlan : Graph preparation graph demand cut.implementations cut.references origin :=
        ⟨occurrences.val,by with_reducible exact occurrences.property,
          by
            change (before.bodies.take count).length = count
            simp only [List.length_take,Nat.min_eq_left enough],
          checked.val,by with_reducible exact checked.property⟩
      return ⟨cut,graphPlan⟩
  else throw .request

structure PrefixResult {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name} (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) (before : Queues) where
  after : Queues
  plans : Prefixes preparation signature actuals before after
  receipts : List (RuntimeGraphOperation.PreparedReceipt preparation)

/-- Every original formal, including an unused one, keeps its own graph read.
The heterogeneous tail is indexed by this exact cut's remaining queues. -/
def readPrefixes {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name} (signature : SourceRuntimeContext.Signature artifact.sources owner name) :
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) →
    (before : Queues) → WorkM (PrefixResult preparation signature actuals before) := fun actuals =>
  Nat.rec (motive := fun _ =>
      (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) →
      (before : Queues) → WorkM (PrefixResult preparation signature actuals before))
    (fun actuals before => match actuals with
      | [] => return ⟨before,.nil before,[]⟩
      | _ :: _ => throw .limit)
    (fun _ next actuals before => match actuals with
      | [] => return ⟨before,.nil before,[]⟩
      | actual :: _ => do
        let first ← readGraph preparation actual.2.graph (RuntimeGraphOperation.required signature actual.1.1) before
        let tail ← next _ first.cut.after
        exactWork (Exact.charge 1)
        return ⟨tail.after,.cons first.cut .unlocated first.graphPlan tail.plans,first.receipt :: tail.receipts⟩)
    actuals.length actuals

structure ArmsResult {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name offset selector target} (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (indices : List (Fin table.arms.length)) (before : Queues) where
  after : Queues
  plans : Arms preparation table indices before after
  receipts : List (RuntimeGraphOperation.PreparedReceipt preparation)

/-- An arm index selects the original table value definitionally; no graph
equality, matrix, label or provider-name lookup selects prepared evidence. -/
def readArms {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name offset selector target} (table : QuantumArms.Table artifact.sources owner name offset selector target) :
    (indices : List (Fin table.arms.length)) → (before : Queues) →
      WorkM (ArmsResult preparation table indices before) := fun indices =>
  Nat.rec (motive := fun _ => (indices : List (Fin table.arms.length)) →
      (before : Queues) → WorkM (ArmsResult preparation table indices before))
    (fun indices before => match indices with
      | [] => return ⟨before,.nil before,[]⟩
      | _ :: _ => throw .limit)
    (fun _ next indices before => match indices with
      | [] => return ⟨before,.nil before,[]⟩
      | index :: _ => do
        let first ← readGraph preparation (table.arms[index]).operation.graph OperationAccess.controllable before
          (.arm (table.arms[index]).operation)
        let tail ← next _ first.cut.after
        exactWork (Exact.charge 1)
        return ⟨tail.after,.cons first.cut first.graphPlan tail.plans,first.receipt :: tail.receipts⟩)
    indices.length indices

end QleisliKernel.Qirf.RuntimeBodyPlanReaders
