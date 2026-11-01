import QleisliKernel.Qirf.FreshEntries
import QleisliKernel.Qirf.PureProviderSubject
import QleisliKernel.Qirf.SourceProviderSubject

/-! Original provider occurrences bound to actual graph subjects.
Function evidence is limited to an exact endomorphic source interface; distinct
ports use actual pure program subjects. Neither lookup nor IR reconstruction
discharges original body, demanded access or Meaning obligations by itself.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceProviderBinding
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Qirf Finite

abbrev Subject := SourceProviderSubject.Subject

def canonical {sources} (provider : StaticOperation.Provider sources) : String :=
  provider.moduleName ++ "::" ++ provider.declarationName

structure Function (artifact : Artifact) (provider : StaticOperation.Provider artifact.sources) (index : Nat) where
  entry : Entry
  identity : Semantics.Function.Identity
  original : artifact.entries[index]? = some entry
  named : entry.implementationName = canonical provider
  samePorts : provider.signature.inputs = provider.signature.outputs
  row : (provider.moduleName,provider.signature.original.source) ∈ identity.sources
  identityRead : ∃ before after, (Qirf.identity artifact entry).run before = (.ok identity,after)

inductive Bound (artifact : Artifact) (provider : StaticOperation.Provider artifact.sources) : Subject → Type
  | function {index : Nat} (binding : Function artifact provider index) : Bound artifact provider (.function index)
  | pure {index : Nat} (program : Semantics.Observation.Program)
      (original : artifact.programs[index]? = some program) : Bound artifact provider (.pure index)

def read (artifact : Artifact) (provider : StaticOperation.Provider artifact.sources) (subject : Subject) :
    WorkM (Bound artifact provider subject) := do
  match subject with
  | .pure index =>
    match original : artifact.programs[index]? with
    | none => throw .request
    | some program => return .pure program original
  | .function index =>
    match original : artifact.entries[index]? with
    | none => throw .request
    | some entry =>
      let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
      guard (artifact.sources.size ≤ 128 && bytes ≤ 1048576 && entry.sources.length ≤ 128) .limit
      guard (entry.implementationName.utf8ByteSize ≤ 4096) .limit
      exactWork (Exact.charge (8*(bytes+4097)*(entry.sources.length+1)))
      let identity ← NaturalAffine.witness (Qirf.identity artifact entry)
      if named : entry.implementationName = canonical provider then
        if samePorts : provider.signature.inputs = provider.signature.outputs then
          if row : (provider.moduleName,provider.signature.original.source) ∈ identity.val.sources then
            return .function ⟨entry,identity.val,original,named,samePorts,row,by with_reducible exact identity.property⟩
          else throw .request
        else throw .request
      else throw .request

def Bound.programIndex {artifact provider subject} : Bound artifact provider subject → Nat
  | .function binding => binding.entry.implementation
  | .pure (index := index) _ _ => index

def Bound.roots {artifact provider subject} : Bound artifact provider subject → List Nat
  | .function (index := index) binding => [binding.entry.implementation,artifact.programs.size+index]
  | .pure (index := index) _ _ => [index]

structure RealizedFunction {artifact provider index}
    (binding : Function artifact provider index) (slots : Slots) where
  receipt : Semantics.ObservingFunction.Receipt
  present : slots[index]?.join = some receipt
  origin : EntryOrigin artifact index receipt

def realizeFunction {artifact provider index nodes slots}
    (binding : Function artifact provider index)
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes slots) :
    WorkM (RealizedFunction binding slots) := do
  match present : slots[index]?.join with
  | none => throw .request
  | some receipt => return ⟨receipt,present,fresh.originalEntry _ _ present⟩

/-- This is only the actual final-dependency IR/code continuation. The enclosing
body request also checks source events, all demanded J/C paths and Meanings. -/
def readIR {artifact provider subject} (root : Validity.Root)
    (bound : Bound artifact provider subject) :
    WorkM (PureProviderSubject.Checked artifact root provider bound.programIndex) :=
  PureProviderSubject.check artifact root provider bound.programIndex

end QleisliKernel.Qirf.SourceProviderBinding
