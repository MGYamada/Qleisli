import QleisliKernel.Qirf.RuntimeProviderHeader

/-! Provider body slots in exact operation-tree occurrence order.
The shared capped per-edge postorder includes every unused actual and a zero
power's child. Duplicate node/evidence indices never remove a body slot. This
stage explicitly refuses pending Meaning requirements; their interleaved
original reference/body equations remain required before complete admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeProviderHeaders
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeProviderHeader (Request)

private def bindingAt {α : Type} (bindings : List (String × α)) (name : String) :
    Except Finite.Error {value : α // (name,value) ∈ bindings} := do
  match read : bindings.filter (·.1 == name) with
  | [(selected,value)] =>
    have kept : (selected,value) ∈ bindings.filter (·.1 == name) := by rw [read]; simp
    have origin := List.mem_filter.mp kept
    have same : selected = name := beq_iff_eq.mp origin.2
    return ⟨value,same ▸ origin.1⟩
  | _ => throw .request

private def readOriginalBindings {α : Type} (names : List String) (bindings : List (String × α)) :
    Except Finite.Error (List {value : α // value ∈ bindings.map Prod.snd}) := do
  if names.length != bindings.length || names.eraseDups.length != names.length then throw .request
  names.mapM fun name => do
    let bound ← bindingAt bindings name
    return ⟨bound.val,List.mem_map_of_mem bound.property⟩

/-- Named wire bindings do not choose the containing function's body order.
Each original formal selects exactly one retained value; equal values under
different formal names remain separate occurrences. -/
def originalBindings {α : Type} (names : List String) (bindings : List (String × α)) :
    Except Finite.Error (List α) :=
  (readOriginalBindings names bindings).map (List.map Subtype.val)

def originalActualSlots {sources owner name original}
    {instantiation : @StaticInstantiation.Checked sources owner name original} {context}
    (arguments : StaticOperation.ArgumentsCheckedWithInstantiation instantiation context) :
    WorkM (List {actual : Sigma (StaticOperation.Actual sources context) // actual ∈ arguments.actuals}) := do
  let names := instantiation.operationNames
  exactWork (Exact.charge (16*(names.length+arguments.actuals.length+1)^2+
    (names.map String.utf8ByteSize).sum+
    (arguments.actuals.map fun actual => actual.1.1.utf8ByteSize).sum))
  let selected ← lift (readOriginalBindings names (arguments.actuals.map fun actual => (actual.1.1,actual)))
  return selected.map fun slot =>
    ⟨slot.val,by
      obtain ⟨entry,present,same⟩ := List.mem_map.mp slot.property
      obtain ⟨actual,original,rfl⟩ := List.mem_map.mp present
      exact same ▸ original⟩

def originalActuals {sources owner name original}
    {instantiation : @StaticInstantiation.Checked sources owner name original} {context}
    (arguments : StaticOperation.ArgumentsCheckedWithInstantiation instantiation context) :
    WorkM (List (Sigma (StaticOperation.Actual sources context))) := do
  return (← originalActualSlots arguments).map Subtype.val

def providerIndices (description : OperationDescription.Description) (occurrences : List Nat) : List Nat :=
  occurrences.filter fun index => match description.nodes[index]? with
    | some (.provider ..) => true
    | _ => false

inductive Reads (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) :
    List Nat → List Request → Type where
  | nil : Reads artifact graph [] []
  | cons {index indices request requests}
      (header : RuntimeProviderHeader.Header artifact graph index request)
      (noPendingMeaning : header.original.supplied.arguments.hasMeaningRequirements = false)
      (rest : Reads artifact graph indices requests) :
      Reads artifact graph (index::indices) (request::requests)

def readHeaders (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) :
    Nat → (indices : List Nat) → (requests : List Request) → WorkM (Reads artifact graph indices requests) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next indices requests => do
    match indices,requests with
    | [],[] => return .nil
    | index::indices,request::requests =>
      let header ← RuntimeProviderHeader.read artifact graph index request
      if noPendingMeaning : header.original.supplied.arguments.hasMeaningRequirements = false then
        let rest ← next indices requests
        return .cons header noPendingMeaning rest
      else throw .request
    | _,_ => throw .request)

structure Checked (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (requests : List Request) where
  noPendingMeaning : graph.hasMeaningRequirements = false
  occurrences : List Nat
  originalOccurrences : RuntimeInterval.Computed (StaticOperation.readOccurrences description) occurrences
  headers : Reads artifact graph (providerIndices description occurrences) requests

def check (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (requests : List Request) :
    WorkM (Checked artifact graph requests) := do
  if noPendingMeaning : graph.hasMeaningRequirements = false then
    let occurrences ← NaturalAffine.witness (StaticOperation.readOccurrences description)
    exactWork (Exact.charge (16*(description.nodes.length+occurrences.val.length+requests.length+1)^2))
    let indices := providerIndices description occurrences.val
    guard (indices.length == requests.length) .request
    let headers ← readHeaders artifact graph (indices.length+1) indices requests
    return ⟨noPendingMeaning,occurrences.val,by with_reducible exact occurrences.property,headers⟩
  else throw .request

def Reads.rows {artifact context description graph indices requests}
    (read : @Reads artifact context description graph indices requests) : List (String × String) :=
  let visit : Nat → {indices : List Nat} → {requests : List Request} →
      Reads artifact graph indices requests → List (String × String) :=
    Nat.rec (fun {_ _} _ => []) (fun _ next {_ _} read => match read with
      | .nil => []
      | .cons header _ rest => header.rows ++ next rest)
  visit indices.length read

def Reads.roots {artifact context description graph indices requests}
    (read : @Reads artifact context description graph indices requests) : List Nat :=
  let visit : Nat → {indices : List Nat} → {requests : List Request} →
      Reads artifact graph indices requests → List Nat :=
    Nat.rec (fun {_ _} _ => []) (fun _ next {_ _} read => match read with
      | .nil => []
      | .cons header _ rest => header.roots ++ next rest)
  visit indices.length read

theorem Reads.count {artifact context description graph indices requests}
    (read : @Reads artifact context description graph indices requests) : indices.length = requests.length := by
  induction read with
  | nil => rfl
  | cons header noPendingMeaning rest ih => simpa using congrArg Nat.succ ih

theorem Checked.noDroppedOccurrence {artifact context description graph requests}
    (checked : @Checked artifact context description graph requests) :
    (providerIndices description checked.occurrences).length = requests.length := checked.headers.count

end QleisliKernel.Qirf.RuntimeProviderHeaders
