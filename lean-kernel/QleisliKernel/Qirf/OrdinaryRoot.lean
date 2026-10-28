import QleisliKernel.SourceTypes.OrdinaryEntry
import QleisliKernel.OrdinaryStorage
import QleisliKernel.Semantics.OrdinaryHistories
import QleisliKernel.Qirf.Validity
import QleisliKernel.Raw.Instrument
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! First closed ordinary-result root component. Reuse the original graph,
Raw ownership/effect/scope gate and complete exact instrument reconstruction.
The original declared type and actual classical output map remain explicit.
No native dispatch, source-body preservation theorem, inverse/control access
or accepted runtime handle is enabled by this component.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.OrdinaryRoot
open Semantics.FiniteCarrier Semantics.OrdinaryValue Semantics.Observation Finite

structure Request where
  selection : SourceTypes.OrdinaryEntry.Selection
  moduleName : String
  declarationName : String
  basis : Basis
  storage : Storage
  publicEffect : Semantics.Raw.Effect

private def collectIds : Nat → Storage → WorkM (List Nat) :=
  Nat.rec (fun _ => throw .limit) (fun _ next storage => do
    exactWork (Exact.charge 1)
    match storage with
    | .unit => pure []
    | .bit id => pure [id]
    | .bits ids | .enumeration _ ids => guard (ids.length ≤ 6) .limit; pure ids
    | .pair first second =>
      let left ← next first
      let right ← next second
      guard (left.length + right.length ≤ 6) .limit
      pure (left ++ right)
    | .tuple fields =>
      guard (fields.length ≤ 128) .limit
      fields.foldlM (fun ids field => do
        let child ← next field
        guard (ids.length + child.length ≤ 6) .limit
        pure (ids ++ child)) []
    | .record _ fields =>
      guard (fields.length ≤ 128) .limit
      fields.foldlM (fun ids field => do
        let child ← next field.2
        guard (ids.length + child.length ≤ 6) .limit
        pure (ids ++ child)) [])

private def hasQuantum : Nat → List Op → Bool :=
  Nat.rec (fun _ => true) (fun _ next operations => operations.any fun operation =>
    match operation with
    | .pure _ | .measure _ _ | .reset _ _ _ | .discard _ => true
    | .branch _ yes no _ _ => next yes || next no
    | _ => false)

private def rank : Semantics.Raw.Effect → Nat
  | .unitary => 0 | .iso => 1 | .observe => 2

private structure Performed {α : Type} (action : WorkM α) where
  result : α
  before : Nat
  after : Nat
  ran : action.run before = (.ok result,after)

-- The witness is made only by this invocation of the original computation,
-- never decoded from a producer success receipt or supplied as an input.
private def perform {α : Type} (action : WorkM α) : WorkM (Performed action) := fun before =>
  match ran : action.run before with
  | (.error error,after) => (.error error,after)
  | (.ok result,after) => (.ok ⟨result,before,after,ran⟩,after)

structure ValuesFor (basis : Basis) (storage : Storage) (histories : List Raw.Instrument.History) where
  values : List Value
  represented : RepresentsAll basis storage (histories.map (·.values)) values

private def historyReaders (basis : Basis) (storage : Storage) :
    Nat → ((histories : List Raw.Instrument.History) → WorkM (ValuesFor basis storage histories)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next histories => do
    match histories with
    | [] => pure ⟨[],.nil⟩
    | first :: rest =>
      let head ← OrdinaryStorage.read first.values basis storage
      let tail ← next rest
      return ⟨head.value :: tail.values,.cons head.represented tail.represented⟩)

def sourceRows (request : Request) (entrySource : String) : List (String × String) :=
  (request.moduleName,entrySource) :: request.basis.filterMap (fun atom => match atom with
    | .enumeration origin _ | .record origin _ => some (origin.moduleName,origin.source)
    | _ => none)

structure Checked (artifact : Artifact) (order : Array Nat) (request : Request) where
  entry : SourceTypes.OrdinaryEntry.Checked artifact.sources request.moduleName request.declarationName
  originalEntry : ∃ before after,
    (SourceTypes.OrdinaryEntry.read artifact.sources request.selection
      request.moduleName request.declarationName).run before = (.ok entry,after)
  declaredResult : entry.basis = request.basis
  root : Validity.Root
  originalRoot : ∃ before after,
    (Validity.checkRootWithSources artifact order (sourceRows request entry.original.source)).run before =
      (.ok root,after)
  instrument : Raw.Instrument.Checked
  reconstructed : ∃ before after,
    (Raw.Instrument.reconstruct root.dependencies root.program []).run before = (.ok instrument,after)
  outputIds : List Nat
  outputStorage : ∃ before after,
    (collectIds 257 request.storage).run before = (.ok outputIds,after)
  outputs : root.program.classicalOutputs = outputIds
  values : ValuesFor request.basis request.storage instrument.histories

/-- Only a first closed classical-result slice. Quantum input/output carriers,
ordinary input domains and full source-preservation remain required elsewhere.
Every actual hidden history is retained; no sampled or normalized subset is
used. Unsupported source rows retain the existing strict coverage refusal. -/
def check (artifact : Artifact) (order : Array Nat) (request : Request) :
    WorkM (Checked artifact order request) := do
  let selected ← perform (SourceTypes.OrdinaryEntry.read artifact.sources request.selection
    request.moduleName request.declarationName)
  let entry := selected.result
  if same : entry.basis = request.basis then
    SourceTypes.checkMany artifact.sources [request.basis]
    let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum
    exactWork (Exact.charge ((bytes+artifact.sources.size+1)*(request.basis.length+2)))
    let root ← perform (Validity.checkRootWithSources artifact order (sourceRows request entry.original.source))
    guard (root.result.program.inputs.isEmpty && root.result.program.classicalInputs.isEmpty &&
      root.result.program.outputs.isEmpty) .request
    guard (!entry.original.parsedHeader.ordinaryOnly ||
      !hasQuantum 65 root.result.program.operations) .request
    match entry.original.parsedHeader.effect with
    | some effect => guard (effect == request.publicEffect) .request
    | none =>
      guard (!entry.original.declaration.isPublic || !hasQuantum 65 root.result.program.operations) .request
      guard (request.publicEffect == root.result.program.effect) .request
    guard (rank root.result.program.effect ≤ rank request.publicEffect) .request
    let ids ← perform (collectIds 257 request.storage)
    exactWork (Exact.charge (ids.result.length+root.result.program.classicalOutputs.length+1))
    if outputs : root.result.program.classicalOutputs = ids.result then
      let reconstructed ← perform (Raw.Instrument.reconstruct root.result.dependencies root.result.program [])
      let values ← historyReaders request.basis request.storage (reconstructed.result.histories.length+1)
        reconstructed.result.histories
      return ⟨entry,⟨selected.before,selected.after,selected.ran⟩,same,
        root.result,⟨root.before,root.after,root.ran⟩,
        reconstructed.result,⟨reconstructed.before,reconstructed.after,reconstructed.ran⟩,
        ids.result,⟨ids.before,ids.after,ids.ran⟩,outputs,values⟩
    else throw .request
  else throw .request

theorem Checked.original_safe {artifact order request} (checked : Checked artifact order request) :
    artifact.programs[artifact.root]? = some checked.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.root.program := by
  obtain ⟨before,after,ran⟩ := checked.originalRoot
  have facts := Validity.checkRootWithSources_postcondition artifact order
    (sourceRows request checked.entry.original.source) checked.root before after ran
  obtain ⟨a,b,verified⟩ := facts.verification
  exact ⟨facts.original,Raw.Observation.verify_ownershipSafe _ _ _ _ _ verified,
    Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

theorem Checked.all_histories {artifact order request} (checked : Checked artifact order request) :
    RepresentsAll request.basis request.storage (checked.instrument.histories.map (·.values))
      checked.values.values := checked.values.represented

theorem Checked.history_count {artifact order request} (checked : Checked artifact order request) :
    checked.instrument.histories.length = checked.values.values.length := by
  simpa only [List.length_map] using checked.values.represented.lengths

theorem Checked.declared_result_read {artifact order request} (checked : Checked artifact order request) :
    ∃ before after, (SourceTypes.typeExpression artifact.sources request.moduleName
      (checked.entry.original.parsedHeader.resultTokens.map (·.text))).run before = (.ok request.basis,after) := by
  obtain ⟨a,b,ran⟩ := checked.originalEntry
  have bound := SourceTypes.OrdinaryEntry.read_result _ _ _ _ _ _ _ ran
  simpa only [checked.declaredResult] using bound

end QleisliKernel.Qirf.OrdinaryRoot
