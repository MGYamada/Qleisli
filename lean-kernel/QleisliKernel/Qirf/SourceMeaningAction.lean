import QleisliKernel.Qirf.SourceMeaningOrdinary
import QleisliKernel.Qirf.SourceMeaningQuantum

/-! Exact actions for an original Meaning graph. Discovery binds each quantum
reference to its own original body and query context. A single final root
supplies all quantum reference actions. Classical leaves use every canonical
input of the original independent ordinary interpreter.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceMeaningAction
open QleisliKernel Finite SourceTypes
open QleisliKernel.Semantics.Exact (Matrix)

private def classicalAction {sources} (kind : SourceMeaningOrdinary.Kind)
    (reference : SourceMeaning.ClassicalReference sources) : SourceMeaning.Action sources :=
  match kind with
  | .permutation => .permutation reference
  | .phase => .phase reference

structure Ordinary {sources} (catalogue : GenericCatalogue.Checked sources)
    (reference : SourceMeaning.ClassicalReference sources) (kind : SourceMeaningOrdinary.Kind)
    (basis : Semantics.FiniteCarrier.Basis) where
  prepared : SourceMeaningOrdinary.Prepared catalogue reference kind basis
  preparation : RuntimeInterval.Computed (SourceMeaningOrdinary.prepare catalogue reference kind basis) prepared
  connected : SourceMeaningOrdinary.Connected prepared
  original : RuntimeInterval.Computed (SourceMeaningOrdinary.connect prepared) connected

private def readOrdinary {sources} (catalogue : GenericCatalogue.Checked sources)
    (reference : SourceMeaning.ClassicalReference sources) (kind : SourceMeaningOrdinary.Kind)
    (basis : Semantics.FiniteCarrier.Basis) : WorkM (Ordinary catalogue reference kind basis) := do
  let original ← NaturalAffine.witness (SourceMeaningOrdinary.prepare catalogue reference kind basis)
  let connected ← NaturalAffine.witness (SourceMeaningOrdinary.connect original.val)
  return ⟨original.val,by with_reducible exact original.property,
    connected.val,by with_reducible exact connected.property⟩

/-- Each constructor is indexed by one node of the actual source graph.
Repeated reference occurrences retain separate provider requests. -/
inductive Node (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {caller owner name} (meaning : SourceMeaning.Checked artifact.sources caller owner name)
    (index : Fin meaning.graph.nodes.length) where
  | quantum (reference : SourceMeaning.QuantumReference artifact.sources)
      (found : (meaning.graph.nodes[index]).action = .reference reference)
      (request : RuntimeProviderHeader.Request)
      (prepared : SourceMeaningQuantum.Prepared artifact ⟨index,reference,found⟩ request)
      (original : RuntimeInterval.Computed
        (SourceMeaningQuantum.prepare artifact (meaning := meaning) ⟨index,reference,found⟩ request) prepared)
  | ordinary (kind : SourceMeaningOrdinary.Kind) (reference : SourceMeaning.ClassicalReference artifact.sources)
      (found : (meaning.graph.nodes[index]).action = classicalAction kind reference)
      (checked : Ordinary catalogue reference kind (meaning.graph.nodes[index]).input.basis)
  | compose (left right : Nat) (found : (meaning.graph.nodes[index]).action = .compose left right)
  | tensor (left right : Nat) (found : (meaning.graph.nodes[index]).action = .tensor left right)

structure Entry (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {caller owner name} (meaning : SourceMeaning.Checked artifact.sources caller owner name) where
  index : Fin meaning.graph.nodes.length
  node : Node artifact catalogue meaning index

def Entry.rows {artifact catalogue caller owner name meaning}
    (entry : @Entry artifact catalogue caller owner name meaning) : List SourceRows.Row :=
  match entry.node with
  | .quantum _ _ _ prepared _ => prepared.rows
  | .ordinary _ _ _ checked => checked.prepared.original.signature.sourceRows ++
      checked.prepared.original.body.checked.summary.staticRows ++ checked.connected.program.sourceRows
  | .compose .. | .tensor .. => []

def Entry.roots {artifact catalogue caller owner name meaning}
    (entry : @Entry artifact catalogue caller owner name meaning) : List Nat :=
  match entry.node with
  | .quantum _ _ _ prepared _ => prepared.roots
  | .ordinary .. | .compose .. | .tensor .. => []

private def readNode (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {caller owner name} (meaning : SourceMeaning.Checked artifact.sources caller owner name)
    (index : Fin meaning.graph.nodes.length) (requests : List RuntimeProviderHeader.Request) :
    WorkM (Node artifact catalogue meaning index × List RuntimeProviderHeader.Request) := do
  let node := meaning.graph.nodes[index]
  match found : node.action with
  | .reference reference =>
    let request :: rest := requests | throw .request
    let prepared ← NaturalAffine.witness
      (SourceMeaningQuantum.prepare artifact (meaning := meaning) ⟨index,reference,found⟩ request)
    return (.quantum reference found request prepared.val (by with_reducible exact prepared.property),rest)
  | .permutation reference =>
    return (.ordinary .permutation reference found (← readOrdinary catalogue reference .permutation node.input.basis),requests)
  | .phase reference =>
    return (.ordinary .phase reference found (← readOrdinary catalogue reference .phase node.input.basis),requests)
  | .compose left right => return (.compose left right found,requests)
  | .tensor left right => return (.tensor left right found,requests)

private def collect (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {caller owner name} (meaning : SourceMeaning.Checked artifact.sources caller owner name)
    (requests : List RuntimeProviderHeader.Request) : WorkM (List (Entry artifact catalogue meaning)) := do
  -- Node lookup in the original linked list and the final index comparison.
  let count := meaning.graph.nodes.length
  exactWork (Exact.charge (16*(count+1)^2+requests.length))
  let (rev,remaining) ← (List.finRange count).foldlM (fun (rev,rest) index => do
    let (prepared,next) ← readNode artifact catalogue meaning index rest
    return (⟨index,prepared⟩ :: rev,next)) ([],requests)
  guard remaining.isEmpty .request
  return rev.reverse

structure Prepared (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {caller owner name} (meaning : SourceMeaning.Checked artifact.sources caller owner name) where
  requests : List RuntimeProviderHeader.Request
  entries : List (Entry artifact catalogue meaning)
  original : RuntimeInterval.Computed (collect artifact catalogue meaning requests) entries
  every : entries.map (·.index) = List.finRange meaning.graph.nodes.length
  relevance : SourceRows.Retained (meaning.graph.sourceRows ++ entries.flatMap Entry.rows)

def Prepared.rows {artifact catalogue caller owner name meaning}
    (prepared : @Prepared artifact catalogue caller owner name meaning) : List SourceRows.Row := prepared.relevance.rows

def Prepared.roots {artifact catalogue caller owner name meaning}
    (prepared : @Prepared artifact catalogue caller owner name meaning) : List Nat := prepared.entries.flatMap Entry.roots

def prepare (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {caller owner name} (meaning : SourceMeaning.Checked artifact.sources caller owner name)
    (requests : List RuntimeProviderHeader.Request) : WorkM (Prepared artifact catalogue meaning) := do
  let entries ← NaturalAffine.witness (collect artifact catalogue meaning requests)
  if every : entries.val.map (·.index) = List.finRange meaning.graph.nodes.length then
    let relevance ← SourceRows.read (meaning.graph.sourceRows ++ entries.val.flatMap Entry.rows)
    return ⟨requests,entries.val,by with_reducible exact entries.property,every,relevance⟩
  else throw .request

/-- Original Meaning nodes are in child-before-parent order. Compute one
matrix per occurrence and preserve the exact left/right ordering of both
products. A missing predecessor is an invalid original graph for this step. -/
private def advance {artifact catalogue caller owner name meaning} (root : Validity.Root) (values : Array Matrix)
    (entry : @Entry artifact catalogue caller owner name meaning) : WorkM (Array Matrix) := do
  let value : Matrix ← match entry.node with
  | .quantum _ _ _ prepared _ => do pure (← SourceMeaningQuantum.read prepared root).action
  | .ordinary _ _ _ checked => pure checked.prepared.candidate
  | .compose left right _ => do
    let first ← lift (readOption values[left]?)
    let second ← lift (readOption values[right]?)
    exactWork (Exact.Matrix.composeWork second first)
  | .tensor left right _ => do
    let first ← lift (readOption values[left]?)
    let second ← lift (readOption values[right]?)
    exactWork (Exact.Matrix.tensorWork first second)
  return values.push value

structure Checked {artifact catalogue caller owner name meaning}
    (prepared : @Prepared artifact catalogue caller owner name meaning) (root : Validity.Root) where
  values : Array Matrix
  calculated : RuntimeInterval.Computed (prepared.entries.foldlM (advance root) #[]) values
  action : Matrix
  atRoot : values[meaning.graph.root]? = some action

def read {artifact catalogue caller owner name meaning}
    (prepared : @Prepared artifact catalogue caller owner name meaning) (root : Validity.Root) :
    WorkM (Checked prepared root) := do
  exactWork (Exact.charge (8*(prepared.entries.length+1)))
  let values ← NaturalAffine.witness (prepared.entries.foldlM (advance root) #[])
  match found : values.val[meaning.graph.root]? with
  | none => throw .request
  | some action => return ⟨values.val,by with_reducible exact values.property,action,found⟩

/-- Both sides retain their original bodies and use the same dependency root.
The enclosing operation supplies the subject and Meaning of the actual request. -/
structure ProviderEquation {artifact context description graph index request header root demand
    catalogue caller owner name meaning prepared}
    (subject : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (specification : @Checked artifact catalogue caller owner name meaning prepared root) : Prop where
  input : subject.paths.ir.original.prepared.ports.domain = meaning.graph.input
  output : subject.paths.ir.original.prepared.ports.codomain = meaning.graph.output
  action : subject.action = specification.action

def compareProvider {artifact context description graph index request header root demand
    catalogue caller owner name meaning prepared}
    (subject : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (specification : @Checked artifact catalogue caller owner name meaning prepared root) :
    WorkM (PLift (ProviderEquation subject specification)) := do
  let ports := subject.paths.ir.original.prepared.ports
  exactWork (Exact.charge (8 * (Raw.OwnerFlow.fields
    [⟨0,ports.domain⟩,⟨0,ports.codomain⟩,⟨0,meaning.graph.input⟩,⟨0,meaning.graph.output⟩] + 1)))
  if samePorts : ports.domain = meaning.graph.input ∧ ports.codomain = meaning.graph.output then
    exactWork (Exact.charge (subject.action.entries.length + specification.action.entries.length + 1))
    if sameAction : subject.action = specification.action then
      return ⟨⟨samePorts.1,samePorts.2,sameAction⟩⟩
    else throw .equation
  else throw .request

end QleisliKernel.Qirf.SourceMeaningAction
