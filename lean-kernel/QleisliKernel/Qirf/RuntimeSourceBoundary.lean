import QleisliKernel.Qirf.RuntimeOwnerMap
import QleisliKernel.RuntimeStorage
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Original source value forests bound to actual retained runtime storage.
The source body is freshly read with its exact checked signature. Input roles
are seeded in original structural order; output roles use the map computed by
the native body continuation. Separate zero-width owners and every tuple level
survive. Ordinary expression/history and quantum code/action checks remain
mandatory; this boundary component alone issues no handle or capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeSourceBoundary
open QleisliKernel QleisliKernel.Finite
open SourceTypes SourceRuntimeValues RuntimeOwnerMap

def summary {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature) : SourceRuntimeContext.Summary signature :=
  body.originalSignature ▸ body.checked.summary

inductive StorageReads : List Semantics.RuntimeType.Tree → List Semantics.RuntimeStorage.Value → Type
  | nil : StorageReads [] []
  | cons {ty stored types stores} (head : QleisliKernel.RuntimeStorage.Checked ty stored)
      (tail : StorageReads types stores) : StorageReads (ty :: types) (stored :: stores)

def readStores : Nat → (types : List Semantics.RuntimeType.Tree) →
    (stores : List Semantics.RuntimeStorage.Value) → WorkM (StorageReads types stores) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next types stores => do
    match types,stores with
    | [],[] => return .nil
    | ty::types,stored::stores =>
      let head ← QleisliKernel.RuntimeStorage.read ty stored
      let tail ← next types stores
      return .cons head tail
    | _,_ => throw .request)

def bindings (roles : List Owner) (owners : List Semantics.CarrierInterface.Owner) : WorkM Map := do
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields roles+1)*(owners.length+1)))
  guard (roles.length == owners.length) .request
  (roles.zip owners).mapM fun (role,owner) => do
    if same : role.basis = owner.basis then return ⟨role,owner.port⟩ else throw .request

structure Inputs {sources owner name signature dependencies program}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (root : RuntimeInterval.Prepared dependencies program)
    (stores : List Semantics.RuntimeStorage.Value) where
  types : StorageReads (signature.parameters.map (·.tree)) stores
  rawInputs : ((stores.flatMap Semantics.RuntimeStorage.quantum).map (·.port)) = program.inputs
  owners : RuntimeOwnerMap.Checked ((summary body).parameterValues.flatMap valueOwners) root.entry
  derived : RuntimeInterval.Computed (do
    let assigned ← bindings ((summary body).parameterValues.flatMap valueOwners)
      (stores.flatMap Semantics.RuntimeStorage.quantum)
    RuntimeOwnerMap.check ((summary body).parameterValues.flatMap valueOwners) root.entry assigned) owners

/-- No owner map is supplied on the wire. It is derived from canonical source
parameters and actual retained ports in the same complete typed forest. -/
def readInputs {sources owner name signature dependencies program}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (root : RuntimeInterval.Prepared dependencies program)
    (stores : List Semantics.RuntimeStorage.Value) : WorkM (Inputs body root stores) := do
  guard (stores.length ≤ 128 && signature.parameters.length ≤ 128) .limit
  exactWork (Exact.charge (32*(program.inputs.length+
    ((summary body).parameterValues.map valueFields).sum+1)))
  let types ← readStores (signature.parameters.length+1) (signature.parameters.map (·.tree)) stores
  if rawInputs : ((stores.flatMap Semantics.RuntimeStorage.quantum).map (·.port)) = program.inputs then
    let owners ← NaturalAffine.witness (do
      let assigned ← bindings ((summary body).parameterValues.flatMap valueOwners)
        (stores.flatMap Semantics.RuntimeStorage.quantum)
      RuntimeOwnerMap.check ((summary body).parameterValues.flatMap valueOwners) root.entry assigned)
    return ⟨types,rawInputs,owners.val,by with_reducible exact owners.property⟩
  else throw .request

def returnedOwners {roles state} (owners : RuntimeOwnerMap.Checked roles state) :
    List Semantics.CarrierInterface.Owner :=
  owners.bindings.map fun binding => ⟨binding.port,binding.owner.basis⟩

structure Outputs (value : SourceRuntimeValues.Value) (state : Raw.Observation.State)
    (owners : RuntimeOwnerMap.Checked (valueOwners value) state)
    (stored : Semantics.RuntimeStorage.Value) (tokens : List Nat) where
  types : QleisliKernel.RuntimeStorage.Checked (typeOf value) stored
  originalOwners : Semantics.RuntimeStorage.quantum stored = returnedOwners owners
  rawOutputs : (Semantics.RuntimeStorage.quantum stored).map (·.port.token) = tokens

/-- Exact original result order is checked after all source body actions.
Swapping two equal-width returned ports changes this equation, including when
both have no wires. Ordinary storage remains subject to its complete separate
source-expression and actual-history checks. -/
def readOutputs (value : SourceRuntimeValues.Value) (state : Raw.Observation.State)
    (owners : RuntimeOwnerMap.Checked (valueOwners value) state)
    (stored : Semantics.RuntimeStorage.Value) (tokens : List Nat) :
    WorkM (Outputs value state owners stored tokens) := do
  exactWork (Exact.charge (32*(valueFields value+
    QleisliKernel.RuntimeStorage.footprint (typeOf value) stored+tokens.length+1)))
  let types ← QleisliKernel.RuntimeStorage.read (typeOf value) stored
  if originalOwners : Semantics.RuntimeStorage.quantum stored = returnedOwners owners then
    if rawOutputs : (Semantics.RuntimeStorage.quantum stored).map (·.port.token) = tokens then
      return ⟨types,originalOwners,rawOutputs⟩
    else throw .request
  else throw .request

def checkOutputs {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature) (state : Raw.Observation.State)
    (owners : RuntimeOwnerMap.Checked (valueOwners (summary body).value) state)
    (stored : Semantics.RuntimeStorage.Value) (tokens : List Nat) :
    WorkM (Outputs (summary body).value state owners stored tokens) :=
  readOutputs (summary body).value state owners stored tokens

theorem Outputs.originalType {value state owners stored tokens}
    (checked : Outputs value state owners stored tokens) :
    Semantics.RuntimeStorage.typeOf stored = typeOf value :=
  checked.types.matched.2

end QleisliKernel.Qirf.RuntimeSourceBoundary
