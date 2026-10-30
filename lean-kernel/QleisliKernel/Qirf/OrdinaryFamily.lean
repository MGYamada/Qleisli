import QleisliKernel.OrdinaryDomain
import QleisliKernel.SourceTypes.OrdinarySignature
import QleisliKernel.OrdinaryStorage
import QleisliKernel.Semantics.OrdinaryHistories
import QleisliKernel.Qirf.Validity
import QleisliKernel.Raw.Instrument
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! Complete ordinary-input/all-hidden-history root checking. Protocol.OrdinaryRoot
and its execution-only QDV gate bind the original graph and request to a fresh
native decision. Source-pattern/body and numerical runtime preservation remain open.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.OrdinaryFamily
open Semantics.FiniteCarrier Semantics.OrdinaryValue Semantics.Observation Finite

structure Request where
  selection : SourceTypes.OrdinarySignature.Selection
  moduleName : String
  declarationName : String
  inputs : List Basis
  inputStorage : List Storage
  inputRows : List (List Bool)
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
      guard (left.length+right.length ≤ 6) .limit
      pure (left ++ right)
    | .tuple fields =>
      guard (fields.length ≤ 128) .limit
      fields.foldlM (fun ids field => do
        let child ← next field
        guard (ids.length+child.length ≤ 6) .limit
        pure (ids ++ child)) []
    | .record _ fields =>
      guard (fields.length ≤ 128) .limit
      fields.foldlM (fun ids field => do
        let child ← next field.2
        guard (ids.length+child.length ≤ 6) .limit
        pure (ids ++ child)) [])

private def inputIds (stores : List Storage) : WorkM (List Nat) := do
  guard (stores.length ≤ 64) .limit
  stores.foldlM (fun ids storage => do
    let child ← collectIds 257 storage
    guard (ids.length+child.length ≤ 6) .limit
    pure (ids ++ child)) []

private structure Performed {α : Type} (action : WorkM α) where
  result : α
  before : Nat
  after : Nat
  ran : action.run before = (.ok result,after)

private def perform {α : Type} (action : WorkM α) : WorkM (Performed action) := fun before =>
  match ran : action.run before with
  | (.error error,after) => (.error error,after)
  | (.ok result,after) => (.ok ⟨result,before,after,ran⟩,after)

structure InputsFor (values : Valuation) (bases : List Basis) (stores : List Storage) where
  items : List Value
  represented : RepresentsMany values bases items stores

private def inputReaders (values : Valuation) :
    Nat → ((bases : List Basis) → (stores : List Storage) → WorkM (InputsFor values bases stores)) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next bases stores => do
    match bases,stores with
    | [],[] => return ⟨[],.nil⟩
    | basis :: bases,store :: stores =>
      let head ← OrdinaryStorage.read values basis store
      let tail ← next bases stores
      return ⟨head.value :: tail.items,.cons basis head.value store bases tail.items stores
        head.represented tail.represented⟩
    | _,_ => throw .request)

structure OutputsFor (basis : Basis) (storage : Storage) (histories : List Raw.Instrument.History) where
  items : List Value
  represented : RepresentsAll basis storage (histories.map (·.values)) items

private def outputReaders (basis : Basis) (storage : Storage) :
    Nat → ((histories : List Raw.Instrument.History) → WorkM (OutputsFor basis storage histories)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next histories => do
    match histories with
    | [] => return ⟨[],.nil⟩
    | first :: rest =>
      let head ← OrdinaryStorage.read first.values basis storage
      let tail ← next rest
      return ⟨head.value :: tail.items,.cons head.represented tail.represented⟩)

structure Row (root : Validity.Root) (request : Request) (assignment : List Bool) where
  inputs : InputsFor (root.program.classicalInputs.zip assignment) request.inputs request.inputStorage
  instrument : Raw.Instrument.Checked
  reconstructed : ∃ before after,
    (Raw.Instrument.reconstruct root.dependencies root.program assignment).run before =
      (.ok instrument,after)
  outputs : OutputsFor request.basis request.storage instrument.histories

inductive Rows (root : Validity.Root) (request : Request) : List (List Bool) → Type
  | nil : Rows root request []
  | cons {assignment : List Bool} {assignments : List (List Bool)}
      (head : Row root request assignment) (tail : Rows root request assignments) :
      Rows root request (assignment :: assignments)

private def rowReaders (root : Validity.Root) (request : Request) :
    Nat → ((assignments : List (List Bool)) → WorkM (Rows root request assignments)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next assignments => do
    match assignments with
    | [] => return .nil
    | assignment :: rest =>
      let inputs ← inputReaders (root.program.classicalInputs.zip assignment) 65
        request.inputs request.inputStorage
      let reconstructed ← perform (Raw.Instrument.reconstruct root.dependencies root.program assignment)
      let outputs ← outputReaders request.basis request.storage
        (reconstructed.result.histories.length+1) reconstructed.result.histories
      let tail ← next rest
      return .cons ⟨inputs,reconstructed.result,
        ⟨reconstructed.before,reconstructed.after,reconstructed.ran⟩,outputs⟩ tail)

private def hasQuantum : Nat → List Op → Bool :=
  Nat.rec (fun _ => true) (fun _ next operations => operations.any fun operation =>
    match operation with
    | .pure _ | .measure _ _ | .reset _ _ _ | .discard _ => true
    | .branch _ yes no _ _ => next yes || next no
    | _ => false)

private def rank : Semantics.Raw.Effect → Nat
  | .unitary => 0 | .iso => 1 | .observe => 2

/-- Shared ordinary components of a mixed runtime interface. These adapters
retain the existing readers and their complete work/error behavior. -/
def storageIds (stores : List Storage) : WorkM (List Nat) := inputIds stores

def readStores (values : Valuation) (bases : List Basis) (stores : List Storage) :
    WorkM (InputsFor values bases stores) := inputReaders values 65 bases stores

def usesQuantum (operations : List Op) : Bool := hasQuantum 65 operations

def effectRank (effect : Semantics.Raw.Effect) : Nat := rank effect

def sourceRows (request : Request) {sources : SourceTypes.Sources}
    (entry : SourceTypes.OrdinarySignature.Checked sources request.moduleName request.declarationName) :
    List (String × String) :=
  (request.moduleName,entry.original.source) :: entry.sourceRows ++
    (request.inputs.flatten ++ request.basis).filterMap (fun atom =>
    match atom with
    | .enumeration origin _ | .record origin _ => some (origin.moduleName,origin.source)
    | _ => none)

/-- Count borrowed signature/type-query paths before projecting their rows.
The source type reads have already bounded these lists and retained paths. -/
def sourceNodes (request : Request) {sources : SourceTypes.Sources}
    (entry : SourceTypes.OrdinarySignature.Checked sources request.moduleName request.declarationName) : Nat :=
  let readNodes := fun (read : SourceTypes.TypeRead sources) =>
    read.resolutions.foldl (fun count resolution => count + 1 + resolution.result.visited.length) 1
  request.inputs.foldl (fun count basis => count + 1 + basis.length) (1 + request.basis.length) +
    entry.parameterReads.foldl (fun count read => count + readNodes read) (readNodes entry.result)

/-- Charge projection/concatenation before allocation and both graph/root
source-coverage scans before their exact original-row comparisons. -/
def sourceRoot (artifact : Artifact) (order : Array Nat) (request : Request)
    (entry : SourceTypes.OrdinarySignature.Checked artifact.sources request.moduleName request.declarationName) :
    WorkM Validity.Root := do
  exactWork (Exact.charge (8 * sourceNodes request entry + 5))
  let extra := sourceRows request entry
  let bytes := (artifact.sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum
  exactWork (Exact.charge (2 * (bytes + artifact.sources.size + 1) * (extra.length + 1)))
  Validity.checkRootWithSources artifact order extra

theorem sourceRoot_result (artifact : Artifact) (order : Array Nat) (request : Request)
    (entry : SourceTypes.OrdinarySignature.Checked artifact.sources request.moduleName request.declarationName)
    (root : Validity.Root) (work left : Nat)
    (ok : (sourceRoot artifact order request entry).run work = (.ok root,left)) :
    ∃ after, (Validity.checkRootWithSources artifact order (sourceRows request entry)).run after =
      (.ok root,left) := by
  obtain ⟨_,charged,_,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,after,_,checked⟩ := bind_success _ _ _ _ _ rest
  exact ⟨after,checked⟩

structure Checked (artifact : Artifact) (order : Array Nat) (request : Request) where
  entry : SourceTypes.OrdinarySignature.Checked artifact.sources request.moduleName request.declarationName
  originalEntry : ∃ before after,
    (SourceTypes.OrdinarySignature.read artifact.sources request.selection
      request.moduleName request.declarationName).run before = (.ok entry,after)
  declaredInputs : entry.inputs = request.inputs
  declaredResult : entry.basis = request.basis
  root : Validity.Root
  originalRoot : ∃ before after,
    (Validity.checkRootWithSources artifact order (sourceRows request entry)).run before =
      (.ok root,after)
  actualInputs : ∃ before after,
    (inputIds request.inputStorage).run before = (.ok root.program.classicalInputs,after)
  actualOutputs : ∃ before after,
    (collectIds 257 request.storage).run before = (.ok root.program.classicalOutputs,after)
  domain : OrdinaryDomain.Checked request.inputs
  suppliedRows : request.inputRows = OrdinaryDomain.assignments domain
  rows : Rows root request (OrdinaryDomain.assignments domain)

/-- Check every independently enumerated canonical input and every hidden
history of its freshly reconstructed original Raw graph. No row subset or
producer-supplied success witness is accepted. -/
def check (artifact : Artifact) (order : Array Nat) (request : Request) :
    WorkM (Checked artifact order request) := do
  let selected ← perform (SourceTypes.OrdinarySignature.read artifact.sources request.selection
    request.moduleName request.declarationName)
  let entry := selected.result
  if inputs : entry.inputs = request.inputs then
    if result : entry.basis = request.basis then
      SourceTypes.checkMany artifact.sources (request.inputs ++ [request.basis])
      let root ← perform (sourceRoot artifact order request entry)
      guard (root.result.program.inputs.isEmpty && root.result.program.outputs.isEmpty) .request
      guard (!entry.original.parsedHeader.ordinaryOnly || !hasQuantum 65 root.result.program.operations) .request
      match entry.original.parsedHeader.effect with
      | some effect => guard (effect == request.publicEffect) .request
      | none =>
        guard (!entry.original.declaration.isPublic || !hasQuantum 65 root.result.program.operations) .request
        guard (request.publicEffect == root.result.program.effect) .request
      guard (rank root.result.program.effect ≤ rank request.publicEffect) .request
      let ids ← perform (inputIds request.inputStorage)
      let outputs ← perform (collectIds 257 request.storage)
      if actualInputs : ids.result = root.result.program.classicalInputs then
        if actualOutputs : outputs.result = root.result.program.classicalOutputs then
          let domain ← OrdinaryDomain.read request.inputs
          if supplied : request.inputRows = OrdinaryDomain.assignments domain then
            let rows ← rowReaders root.result request (domain.code.labels.length+1)
              (OrdinaryDomain.assignments domain)
            return ⟨entry,⟨selected.before,selected.after,selected.ran⟩,inputs,result,
              root.result,(by
                obtain ⟨before,ran⟩ := sourceRoot_result artifact order request entry
                  root.result root.before root.after root.ran
                exact ⟨before,root.after,ran⟩),
              ⟨ids.before,ids.after,actualInputs ▸ ids.ran⟩,
              ⟨outputs.before,outputs.after,actualOutputs ▸ outputs.ran⟩,domain,supplied,rows⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

theorem Checked.original_safe {artifact order request} (checked : Checked artifact order request) :
    artifact.programs[artifact.root]? = some checked.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.root.program := by
  obtain ⟨before,after,ran⟩ := checked.originalRoot
  have facts := Validity.checkRootWithSources_postcondition artifact order
    (sourceRows request checked.entry) checked.root before after ran
  obtain ⟨a,b,verified⟩ := facts.verification
  exact ⟨facts.original,Raw.Observation.verify_ownershipSafe _ _ _ _ _ verified,
    Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

theorem Rows.contains {root request assignments} (rows : Rows root request assignments)
    {assignment : List Bool} (member : assignment ∈ assignments) :
    Nonempty (Row root request assignment) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst assignment; exact ⟨head⟩
    · exact ih later

theorem Checked.every_canonical_input {artifact order request} (checked : Checked artifact order request)
    (code : Nat) (member : code ∈ checked.domain.code.labels) :
    ∃ assignment, Semantics.OrdinaryValue.littleEndian assignment = code ∧
      Nonempty (Row checked.root request assignment) := by
  obtain ⟨assignment,found,same⟩ := OrdinaryDomain.complete checked.domain code member
  exact ⟨assignment,same,checked.rows.contains found⟩

theorem Row.all_hidden_histories {root request assignment} (row : Row root request assignment) :
    RepresentsAll request.basis request.storage (row.instrument.histories.map (·.values))
      row.outputs.items := row.outputs.represented

end QleisliKernel.Qirf.OrdinaryFamily
