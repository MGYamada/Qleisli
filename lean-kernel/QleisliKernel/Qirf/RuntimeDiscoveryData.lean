import QleisliKernel.Qirf.RuntimeProviderHeader
import QleisliKernel.Qirf.RuntimeProviderHeaders
import QleisliKernel.Qirf.RuntimeGraphOperation
import QleisliKernel.Qirf.RuntimeStaticPrimitive
import QleisliKernel.SourceTypes.QuantumArms
import QleisliKernel.SourceTypes.GenericCatalogue
import QleisliKernel.Qirf.SourcePendingMeaning

/-! Discover every original runtime body before the one fresh graph check.
The traversal follows actual source events and supplied context occurrences;
provider bodies retain their original supplier receipts. A discovery result is
not source/IR acceptance: local action, ordinary history, Meaning and access
continuations must still be checked under the final root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyDiscovery
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues
abbrev Context := RuntimeContextRequest.Context
abbrev BodyRequest := RuntimeProviderHeader.Request

structure Discovery where
  rows : List (String × String) := []
  roots : List Nat := []

def Discovery.append (first second : Discovery) : Discovery :=
  ⟨first.rows ++ second.rows,first.roots ++ second.roots⟩

def subjectRoots (artifact : Artifact) : SourceProviderSubject.Subject → WorkM (List Nat)
  | .pure index => do
    let _ ← lift (readOption artifact.programs[index]?)
    return [index]
  | .function index => do
    let entry ← lift (readOption artifact.entries[index]?)
    let _ ← lift (readOption artifact.programs[entry.implementation]?)
    return [entry.implementation,artifact.programs.size+index]

/-- Coherent ordinary helper bodies contribute original source queries rather
than fabricated runtime call intervals. Their actual finite reference/action
correspondence is checked by the separate basis continuation. -/
def ordinaryRows (sources : Sources) : Nat → {owner : String} →
    List (SourceRuntimeContext.Event sources owner) → WorkM (List (String × String)) :=
  Nat.rec (fun {_} _ => throw .limit) (fun _ next {_} events => do
    events.foldlM (fun rows event => do
      match event with
      | .primitive call =>
        guard (call.kind == .emptyBits) .request
        return rows ++ CallName.sourceRows call.candidate
      | .named event =>
        guard (event.target.signature.arguments.operations.isEmpty &&
          !event.target.signature.operations.hasMeaningRequirements) .request
        let source ← SourceRuntimeTrace.readNamedBody event
        guard (!source.checked.summary.quantumUse && source.checked.summary.allocated.isEmpty &&
          source.checked.summary.consumed.isEmpty &&
          source.checked.summary.inferredEffect == .unitary) .request
        let children ← next source.checked.events
        return rows ++ event.target.sourceRows ++ source.checked.signature.sourceRows ++
          source.checked.summary.staticRows ++ children
      | .matching event arms =>
        exactWork (Exact.charge (16*(arms.length+event.arms.length+1)))
        guard (arms.length == event.arms.length && event.arms.all (fun arm =>
          arm.2.inferredEffect == .unitary && !arm.2.quantumUse &&
          arm.2.allocated.isEmpty && arm.2.consumed.isEmpty)) .request
        let children ← arms.foldlM (fun collected arm => do
          let child ← next arm
          exactWork (Exact.charge (collected.length+child.length+1))
          return collected ++ child) []
        return rows ++ event.labels.labels.sourceRows ++ children
      | .registerPrimitive event =>
        guard (event.kind == .prependBit && event.allocated.isEmpty && event.consumed.isEmpty) .request
        return rows ++ (SourceRuntimeContext.Event.registerPrimitive event).staticRows
      | .primitive event =>
        guard (event.kind == .emptyBits && event.allocated.isEmpty && event.consumed.isEmpty) .request
        return rows ++ CallName.sourceRows event.candidate
      | _ => throw .request) [] )

inductive OperationMode (artifact : Artifact) where
  | strict
  | extended (continuation : RuntimeGraphOperation.Preparation artifact)

def OperationMode.Receipt {artifact} : OperationMode artifact → Type
  | .strict => Empty
  | .extended continuation => RuntimeGraphOperation.PreparedReceipt continuation

def OperationMode.takeReferences {artifact} (mode : OperationMode artifact) (explicit : Bool)
    (references : List (List (List BodyRequest))) :
    WorkM (List (List BodyRequest) × List (List (List BodyRequest))) := do
  match mode with
  | .strict =>
    if explicit then
      let group :: remaining := references | throw .request
      guard group.isEmpty .request
      return ([],remaining)
    else
      guard references.isEmpty .request
      return ([],[])
  | .extended _ =>
    let group :: remaining := references | throw .request
    return (group,remaining)

def OperationMode.checkSignature {artifact} (mode : OperationMode artifact) {owner name}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name) (hasOriginalCaller : Bool) : WorkM Unit :=
  match mode with
  | .strict => guard (!signature.operations.hasMeaningRequirements) .request
  | .extended _ => guard (hasOriginalCaller || signature.operations.rootRequirements.isEmpty) .request


end QleisliKernel.Qirf.RuntimeBodyDiscovery
