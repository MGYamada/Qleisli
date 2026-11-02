import QleisliKernel.Qirf.RuntimeProviderPaths
import QleisliKernel.Qirf.RuntimeProviderHeaders

/-! Consume every demanded provider occurrence of one original operation tree.
Demand order comes from the independent per-edge access traversal, never from
an index-union or unique-provider cache. Source-body and Meaning derivations
remain separate mandatory continuations of the recursive runtime body checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOperationPaths
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
abbrev Request := RuntimeProviderHeader.Request

inductive Bound {artifact : Artifact} {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (root : Validity.Root) :
    (demands : List (Nat × StaticOperation.Paths)) → {indices : List Nat} → {requests : List Request} →
    RuntimeProviderHeaders.Reads artifact graph indices requests → Type where
  | nil : Bound graph root [] RuntimeProviderHeaders.Reads.nil
  | cons {index indices request requests demand}
      {header : RuntimeProviderHeader.Header artifact graph index request}
      {noPendingMeaning : header.original.supplied.arguments.hasMeaningRequirements = false}
      {rest : RuntimeProviderHeaders.Reads artifact graph indices requests}
      {demands : List (Nat × StaticOperation.Paths)}
      (head : RuntimeProviderPaths.Checked header root demand)
      (tail : Bound graph root demands rest) :
      Bound graph root ((index,demand)::demands) (.cons header noPendingMeaning rest)

def readAll {artifact : Artifact} {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (root : Validity.Root) :
    Nat → (demands : List (Nat × StaticOperation.Paths)) → {indices : List Nat} → {requests : List Request} →
    (headers : RuntimeProviderHeaders.Reads artifact graph indices requests) → WorkM (Bound graph root demands headers) :=
  Nat.rec (fun _ {_ _} _ => throw .limit) (fun _ next demands {_ _} headers => do
    exactWork (Exact.charge 1)
    match headers,demands with
    | .nil,[] => return .nil
    | .cons (index := index) header noPending rest,(expected,demand)::demands =>
      if same : expected = index then
        let head ← RuntimeProviderPaths.read header root demand
        let tail ← next demands rest
        let actual : Bound graph root ((index,demand)::demands) (.cons header noPending rest) := .cons head tail
        pure (Eq.mp (congrArg (fun wanted =>
          Bound graph root ((wanted,demand)::demands) (.cons header noPending rest)) same.symm) actual)
      else throw .request
    | _,_ => throw .request)

def providerDemands {sources context description graph requested}
    (access : @OperationAccess.CheckedOccurrences sources context description graph requested) :
    List (Nat × StaticOperation.Paths) := access.providers.map fun (index,_,paths) => (index,paths)

structure Checked {artifact : Artifact} {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (root : Validity.Root)
    (requested : StaticOperation.Paths) (requests : List Request) where
  headers : RuntimeProviderHeaders.Checked artifact graph requests
  access : OperationAccess.CheckedOccurrences graph requested
  bodies : Bound graph root (providerDemands access) headers.headers

def read {artifact : Artifact} {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (root : Validity.Root)
    (requested : StaticOperation.Paths) (requests : List Request) :
    WorkM (Checked graph root requested requests) := do
  let headers ← RuntimeProviderHeaders.check artifact graph requests
  let access ← OperationAccess.checkOccurrences graph requested
  let bodies ← readAll graph root (access.providers.length+1) (providerDemands access) headers.headers
  return ⟨headers,access,bodies⟩

/-- Visit the actual checked header at every occurrence. The callback never
searches by name, descriptor, width or matrix to recover a supplying context. -/
def Bound.mapM {artifact : Artifact} {context description graph root} {α : Type}
    (visit : {index : Nat} → {request : Request} →
      (header : @RuntimeProviderHeader.Header artifact context description graph index request) →
      (demand : StaticOperation.Paths) → RuntimeProviderPaths.Checked header root demand → WorkM α) :
    {demands : List (Nat × StaticOperation.Paths)} → {indices : List Nat} → {requests : List Request} →
    {headers : RuntimeProviderHeaders.Reads artifact graph indices requests} →
    Bound graph root demands headers → WorkM (List α)
  | _,_,_,_,.nil => pure []
  | _,_,_,_,.cons (header := header) (demand := demand) head rest => do
    let first ← visit header demand head
    let tail ← rest.mapM visit
    return first :: tail

def Bound.logicals {artifact : Artifact} {context description graph root demands indices requests headers}
    (bound : @Bound artifact context description graph root demands indices requests headers) : List Semantics.Exact.Matrix :=
  match bound with
  | .nil => []
  | .cons head rest => head.ir.original.prepared.equations.action :: rest.logicals

theorem Bound.allOccurrences {artifact : Artifact} {context description graph root demands indices requests headers}
    (bound : @Bound artifact context description graph root demands indices requests headers) :
    bound.logicals.length = requests.length := by
  induction bound with
  | nil => rfl
  | cons head rest ih => simpa only [Bound.logicals,List.length_cons] using congrArg Nat.succ ih

end QleisliKernel.Qirf.RuntimeOperationPaths
