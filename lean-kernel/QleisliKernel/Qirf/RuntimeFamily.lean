import QleisliKernel.Qirf.OrdinaryFamily
import QleisliKernel.Qirf.Carrier
import QleisliKernel.SourceTypes.RuntimeSignature
import QleisliKernel.RuntimeStorage
import QleisliKernel.CodeSpace

/-! Original full runtime interfaces over one freshly checked Raw graph.
Ordinary fields reuse complete canonical input/history checking; quantum fields
add exact per-history code-space and logical Gram checks. The dense instrument
component retains its existing six-bit limit. Wider qmatch integration remains
a separate use of the existing sector proofs, not a dense-matrix fallback.
This component has no native dispatcher or source execution authority yet.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeFamily
open Finite Semantics.FiniteCarrier Semantics.RuntimeStorage Semantics.OrdinaryValue

structure Request where
  selection : SourceTypes.OrdinarySignature.Selection
  moduleName : String
  declarationName : String
  parameters : List Semantics.RuntimeType.Tree
  inputStorage : List Semantics.RuntimeStorage.Value
  inputRows : List (List Bool)
  result : Semantics.RuntimeType.Tree
  storage : Semantics.RuntimeStorage.Value
  publicEffect : Semantics.Raw.Effect

def inputValues (request : Request) : List (Basis × Storage) :=
  request.inputStorage.flatMap Semantics.RuntimeStorage.ordinary

def outputValues (request : Request) : List (Basis × Storage) :=
  Semantics.RuntimeStorage.ordinary request.storage

def inputOwners (request : Request) : List Semantics.CarrierInterface.Owner :=
  request.inputStorage.flatMap Semantics.RuntimeStorage.quantum

def outputOwners (request : Request) : List Semantics.CarrierInterface.Owner :=
  Semantics.RuntimeStorage.quantum request.storage

private structure Performed {α : Type} (action : WorkM α) where
  result : α
  before : Nat
  after : Nat
  ran : action.run before = (.ok result,after)

private def perform {α : Type} (action : WorkM α) : WorkM (Performed action) := fun before =>
  match ran : action.run before with
  | (.error error,after) => (.error error,after)
  | (.ok result,after) => (.ok ⟨result,before,after,ran⟩,after)

inductive StorageReads : List Semantics.RuntimeType.Tree → List Semantics.RuntimeStorage.Value → Type
  | nil : StorageReads [] []
  | cons {ty stored types stores} (head : QleisliKernel.RuntimeStorage.Checked ty stored)
      (tail : StorageReads types stores) : StorageReads (ty :: types) (stored :: stores)

private def readInputs : Nat → (types : List Semantics.RuntimeType.Tree) →
    (stores : List Semantics.RuntimeStorage.Value) → WorkM (StorageReads types stores) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse types stores => do
    match types,stores with
    | [],[] => pure .nil
    | ty :: types,store :: stores =>
      let head ← QleisliKernel.RuntimeStorage.read ty store
      let tail ← recurse types stores
      pure (.cons head tail)
    | _,_ => throw .request)

/-- Physical width alone never makes a logical rectangular map Unitary, and
actual observation never disappears when its code dimension is one. -/
def logicalEffect (physical : Semantics.Raw.Effect) (input output : Nat) : Semantics.Raw.Effect :=
  if physical == .observe then .observe
  else if physical == .iso || input != output then .iso else .unitary

def annotationAllowed (declared : Option Semantics.Raw.Effect) (isPublic quantum : Bool)
    (requested : Semantics.Raw.Effect) : Bool :=
  match declared with
  | some effect => requested == effect
  | none => !isPublic || !quantum

def sourceRows (request : Request) {sources : SourceTypes.Sources}
    (entry : SourceTypes.RuntimeSignature.Checked sources request.moduleName request.declarationName) :
    List (String × String) :=
  entry.sourceRows ++
    ((request.inputStorage.flatMap Semantics.RuntimeStorage.bases) ++
      Semantics.RuntimeStorage.bases request.storage).flatten.filterMap fun atom =>
      match atom with
      | .enumeration origin _ | .record origin _ => some (origin.moduleName,origin.source)
      | _ => none

private def sourceRoot (artifact : Artifact) (order : Array Nat) (request : Request)
    (entry : SourceTypes.RuntimeSignature.Checked artifact.sources request.moduleName request.declarationName) :
    WorkM Validity.Root := do
  let queryNodes := fun (query : SourceTypes.TypeRead artifact.sources) =>
    query.resolutions.foldl (fun count resolution => count+resolution.result.visited.length+1) 1
  let storedNodes := fun (store : Semantics.RuntimeStorage.Value) =>
    store.foldl (fun count atom => count+1+match atom with
      | .ordinary basis _ => basis.length
      | .quantum owner => owner.basis.length
      | .tuple _ => 0) 0
  let nodes := entry.parameters.foldl (fun count part =>
    count+part.tree.length+part.queries.foldl (fun count query => count+queryNodes query) 0)
    (entry.result.tree.length+entry.result.queries.foldl (fun count query => count+queryNodes query) 0) +
    request.inputStorage.foldl (fun count store => count+storedNodes store) (storedNodes request.storage)
  -- Reserve every input/result query path and stored nominal origin before
  -- allocating rows, then charge actual byte comparisons at the common root.
  exactWork (Exact.charge (8*nodes+5))
  let extra := sourceRows request entry
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  exactWork (Exact.charge (2*(bytes+artifact.sources.size+1)*(extra.length+1)))
  Validity.checkRootWithSources artifact order extra

private theorem sourceRoot_result (artifact : Artifact) (order : Array Nat) (request : Request)
    (entry : SourceTypes.RuntimeSignature.Checked artifact.sources request.moduleName request.declarationName)
    (root : Validity.Root) (work left : Nat)
    (ok : (sourceRoot artifact order request entry).run work = (.ok root,left)) :
    ∃ after, (Validity.checkRootWithSources artifact order (sourceRows request entry)).run after = (.ok root,left) := by
  obtain ⟨_,charged,_,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,after,_,checked⟩ := bind_success _ _ _ _ _ rest
  exact ⟨after,checked⟩

inductive Outputs (bases : List Basis) (stores : List Storage) : List Raw.Instrument.History → Type
  | nil : Outputs bases stores []
  | cons {history rest} (head : OrdinaryFamily.InputsFor history.values bases stores)
      (tail : Outputs bases stores rest) : Outputs bases stores (history :: rest)

private def readOutputs (bases : List Basis) (stores : List Storage) : Nat →
    (histories : List Raw.Instrument.History) → WorkM (Outputs bases stores histories) :=
  Nat.rec (fun _ => throw .limit) (fun _ recurse histories => do
    match histories with
    | [] => pure .nil
    | first :: rest =>
      let head ← OrdinaryFamily.readStores first.values bases stores
      let tail ← recurse rest
      pure (.cons head tail))

structure Row (root : Validity.Root) (request : Request) (inputCode outputCode : Semantics.Exact.Matrix)
    (assignment : List Bool) where
  inputs : OrdinaryFamily.InputsFor (root.program.classicalInputs.zip assignment)
    ((inputValues request).map (·.1)) ((inputValues request).map (·.2))
  instrument : Raw.Instrument.Checked
  reconstructed : ∃ before after,
    (Raw.Instrument.reconstruct root.dependencies root.program assignment).run before = (.ok instrument,after)
  outputs : Outputs ((outputValues request).map (·.1)) ((outputValues request).map (·.2)) instrument.histories
  code : CodeSpace.Checked inputCode outputCode instrument.histories

inductive Rows (root : Validity.Root) (request : Request) (inputCode outputCode : Semantics.Exact.Matrix) :
    List (List Bool) → Type
  | nil : Rows root request inputCode outputCode []
  | cons {assignment rest} (head : Row root request inputCode outputCode assignment)
      (tail : Rows root request inputCode outputCode rest) : Rows root request inputCode outputCode (assignment :: rest)

private def readRows (root : Validity.Root) (request : Request) (inputCode outputCode : Semantics.Exact.Matrix) :
    Nat → (assignments : List (List Bool)) → WorkM (Rows root request inputCode outputCode assignments) :=
  Nat.rec (fun _ => throw .limit) (fun _ recurse assignments => do
    match assignments with
    | [] => pure .nil
    | first :: rest =>
      let inputs ← OrdinaryFamily.readStores (root.program.classicalInputs.zip first)
        ((inputValues request).map (·.1)) ((inputValues request).map (·.2))
      let instrument ← perform (Raw.Instrument.reconstruct root.dependencies root.program first)
      let outputs ← readOutputs ((outputValues request).map (·.1)) ((outputValues request).map (·.2))
        (instrument.result.histories.length+1) instrument.result.histories
      let code ← CodeSpace.read inputCode outputCode instrument.result.histories
      let tail ← recurse rest
      pure (.cons ⟨inputs,instrument.result,⟨instrument.before,instrument.after,instrument.ran⟩,outputs,code⟩ tail))

structure Checked (artifact : Artifact) (order : Array Nat) (request : Request) where
  entry : SourceTypes.RuntimeSignature.Checked artifact.sources request.moduleName request.declarationName
  originalEntry : ∃ before after,
    (SourceTypes.RuntimeSignature.read artifact.sources request.moduleName request.declarationName).run before =
      (.ok entry,after)
  selection : SourceTypes.OrdinarySignature.selectionAllowed request.selection entry.original = true
  parameterTypes : entry.parameters.map (·.tree) = request.parameters
  resultType : entry.result.tree = request.result
  inputStorage : StorageReads request.parameters request.inputStorage
  outputStorage : QleisliKernel.RuntimeStorage.Checked request.result request.storage
  root : Validity.Root
  originalRoot : ∃ before after,
    (Validity.checkRootWithSources artifact order (sourceRows request entry)).run before = (.ok root,after)
  inputCode : Semantics.Exact.Matrix
  outputCode : Semantics.Exact.Matrix
  inputCodeRead : ∃ before after,
    (Carrier.ownerCode (inputOwners request)).run before = (.ok inputCode,after)
  outputCodeRead : ∃ before after,
    (Carrier.ownerCode (outputOwners request)).run before = (.ok outputCode,after)
  actualInputs : root.program.inputs = (inputOwners request).map (·.port)
  actualOutputs : root.program.outputs = (outputOwners request).map (·.port.token)
  liveOutputs : (outputOwners request).all (fun owner => root.checked.state.quantum.live.contains owner.port) = true
  ordinaryInputs : ∃ before after,
    (OrdinaryFamily.storageIds ((inputValues request).map (·.2))).run before = (.ok root.program.classicalInputs,after)
  ordinaryOutputs : ∃ before after,
    (OrdinaryFamily.storageIds ((outputValues request).map (·.2))).run before = (.ok root.program.classicalOutputs,after)
  classicalBody : (!entry.original.parsedHeader.ordinaryOnly ||
    !OrdinaryFamily.usesQuantum root.program.operations) = true
  annotation : annotationAllowed entry.original.parsedHeader.effect entry.original.declaration.isPublic
    (OrdinaryFamily.usesQuantum root.program.operations) request.publicEffect = true
  effectBound : OrdinaryFamily.effectRank (logicalEffect root.program.effect inputCode.cols outputCode.cols) ≤
    OrdinaryFamily.effectRank request.publicEffect
  domain : OrdinaryDomain.Checked ((inputValues request).map (·.1))
  suppliedRows : request.inputRows = OrdinaryDomain.assignments domain
  rows : Rows root request inputCode outputCode (OrdinaryDomain.assignments domain)

/-- Inspect one exact original root. The source header supplies types and the
public boundary; the actual Raw body supplies effects and every Kraus map.
No producer row subset, sampled history, projected padding or physical-width
argument may substitute for these checks. -/
def check (artifact : Artifact) (order : Array Nat) (request : Request) :
    WorkM (Checked artifact order request) := do
  guard (request.parameters.length ≤ 64 && request.inputStorage.length ≤ 64 &&
    (request.parameters.map List.length).sum ≤ 3*128 && request.result.length ≤ 3*128 &&
    (request.inputStorage.map List.length).sum ≤ 3*128 && request.storage.length ≤ 3*128) .limit
  let metadata := request.parameters.foldl (fun count ty =>
    count+QleisliKernel.RuntimeStorage.footprint ty [])
      (QleisliKernel.RuntimeStorage.footprint request.result request.storage) +
    request.inputStorage.foldl (fun count store =>
      count+QleisliKernel.RuntimeStorage.footprint [] store) 0
  exactWork (Exact.charge (16*(metadata+1)))
  let original ← perform (SourceTypes.RuntimeSignature.read artifact.sources request.moduleName request.declarationName)
  let entry := original.result
  if selected : SourceTypes.OrdinarySignature.selectionAllowed request.selection entry.original = true then
    if parameters : entry.parameters.map (·.tree) = request.parameters then
      if result : entry.result.tree = request.result then
        let inputs ← readInputs 65 request.parameters request.inputStorage
        let output ← QleisliKernel.RuntimeStorage.read request.result request.storage
        SourceTypes.checkMany artifact.sources
          (request.inputStorage.flatMap Semantics.RuntimeStorage.bases ++ Semantics.RuntimeStorage.bases request.storage)
        let root ← perform (sourceRoot artifact order request entry)
        let inputCode ← perform (Carrier.ownerCode (inputOwners request))
        let outputCode ← perform (Carrier.ownerCode (outputOwners request))
        if actualInputs : root.result.program.inputs = (inputOwners request).map (·.port) then
          if actualOutputs : root.result.program.outputs = (outputOwners request).map (·.port.token) then
            if live : (outputOwners request).all
                (fun owner => root.result.checked.state.quantum.live.contains owner.port) = true then
              let ordinaryInputs ← perform (OrdinaryFamily.storageIds ((inputValues request).map (·.2)))
              let ordinaryOutputs ← perform (OrdinaryFamily.storageIds ((outputValues request).map (·.2)))
              if inputIds : ordinaryInputs.result = root.result.program.classicalInputs then
                if outputIds : ordinaryOutputs.result = root.result.program.classicalOutputs then
                  if classical : (!entry.original.parsedHeader.ordinaryOnly ||
                      !OrdinaryFamily.usesQuantum root.result.program.operations) = true then
                    if annotated : annotationAllowed entry.original.parsedHeader.effect
                        entry.original.declaration.isPublic (OrdinaryFamily.usesQuantum root.result.program.operations)
                        request.publicEffect = true then
                      if effects : OrdinaryFamily.effectRank
                          (logicalEffect root.result.program.effect inputCode.result.cols outputCode.result.cols) ≤
                            OrdinaryFamily.effectRank request.publicEffect then
                        let domain ← OrdinaryDomain.read ((inputValues request).map (·.1))
                        if supplied : request.inputRows = OrdinaryDomain.assignments domain then
                          let rows ← readRows root.result request inputCode.result outputCode.result
                            (domain.code.labels.length+1) (OrdinaryDomain.assignments domain)
                          return {
                            entry, originalEntry := ⟨original.before,original.after,original.ran⟩,
                            selection := selected, parameterTypes := parameters, resultType := result,
                            inputStorage := inputs, outputStorage := output, root := root.result,
                            originalRoot := (by
                              obtain ⟨before,ran⟩ := sourceRoot_result artifact order request entry
                                root.result root.before root.after root.ran
                              exact ⟨before,root.after,ran⟩),
                            inputCode := inputCode.result, outputCode := outputCode.result,
                            inputCodeRead := ⟨inputCode.before,inputCode.after,inputCode.ran⟩,
                            outputCodeRead := ⟨outputCode.before,outputCode.after,outputCode.ran⟩,
                            actualInputs, actualOutputs, liveOutputs := live,
                            ordinaryInputs := ⟨ordinaryInputs.before,ordinaryInputs.after,inputIds ▸ ordinaryInputs.ran⟩,
                            ordinaryOutputs := ⟨ordinaryOutputs.before,ordinaryOutputs.after,outputIds ▸ ordinaryOutputs.ran⟩,
                            classicalBody := classical, annotation := annotated, effectBound := effects,
                            domain, suppliedRows := supplied, rows }
                        else throw .request
                      else throw .request
                    else throw .request
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
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

theorem Checked.unitary_logical_dimensions {artifact order request}
    (checked : Checked artifact order request) (unitary : request.publicEffect = .unitary) :
    checked.inputCode.cols = checked.outputCode.cols := by
  by_cases same : checked.inputCode.cols = checked.outputCode.cols
  · exact same
  · have bound := checked.effectBound
    rw [unitary] at bound
    cases effect : checked.root.program.effect <;>
      simp [logicalEffect,effect,same,OrdinaryFamily.effectRank] at bound <;>
      exact (Nat.not_succ_le_zero _ bound).elim

theorem Rows.contains {root request inputCode outputCode assignments}
    (rows : Rows root request inputCode outputCode assignments) {assignment : List Bool}
    (member : assignment ∈ assignments) : Nonempty (Row root request inputCode outputCode assignment) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst assignment; exact ⟨head⟩
    · exact ih later

theorem Checked.every_canonical_input {artifact order request} (checked : Checked artifact order request)
    (code : Nat) (member : code ∈ checked.domain.code.labels) :
    ∃ assignment, Semantics.OrdinaryValue.littleEndian assignment = code ∧
      Nonempty (Row checked.root request checked.inputCode checked.outputCode assignment) := by
  obtain ⟨assignment,found,same⟩ := OrdinaryDomain.complete checked.domain code member
  exact ⟨assignment,same,checked.rows.contains found⟩

theorem Outputs.contains {bases stores histories} (outputs : Outputs bases stores histories)
    {history : Raw.Instrument.History} (member : history ∈ histories) :
    Nonempty (OrdinaryFamily.InputsFor history.values bases stores) := by
  induction outputs with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst history; exact ⟨head⟩
    · exact ih later

theorem Row.every_hidden_history {root request inputCode outputCode assignment}
    (row : Row root request inputCode outputCode assignment) {history : Raw.Instrument.History}
    (member : history ∈ row.instrument.histories) :
    Nonempty (OrdinaryFamily.InputsFor history.values ((outputValues request).map (·.1))
      ((outputValues request).map (·.2))) ∧
      Nonempty (CodeSpace.Map inputCode outputCode history.operator) :=
  ⟨row.outputs.contains member,row.code.maps.every_history member⟩

end QleisliKernel.Qirf.RuntimeFamily
