import QleisliKernel.Qirf.RuntimeAccessInterval
import QleisliKernel.SourceTypes.ParameterPatterns
import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.SourceTypes.LexicalNatural

/-! Derive the entry access frame from the original function header and the
actual Raw root. This straight-line reader keeps the written calls and suffix.
The caller still needs callee correspondence and inter-call restoration.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeAccessSource
open QleisliKernel Finite SourceTypes
open SourceTypes.AccessSyntax

private def finiteAtom : Semantics.FiniteCarrier.Atom → Option Semantics.Finite.Atom
  | .unit => some .unit
  | .bit => some .bit
  | .bits n => some (.bits n)
  | .pair => some .pair
  | .tuple n => some (.tuple n)
  | .enumeration .. | .record .. => none

/-- Keep the exact original basis and actual Raw port, including the token
identity of a zero-width owner. Width is checked after the typed pairing. -/
structure Parameter where
  original : Owner
  port : Semantics.Raw.Port

private def parameter (row : (List LocatedToken × Semantics.FiniteCarrier.Basis) × Semantics.Raw.Port) :
    Option Parameter := do
  let (([binder],declared),port) := row | none
  if !identifier binder.text then none else do
    let basis ← declared.mapM finiteAtom
    if Semantics.Finite.width basis == port.bits && port.bits == port.wires.length then
      some ⟨⟨binder,basis,port.wires⟩,port⟩
    else none

def parameters (patterns : List (List LocatedToken)) (bases : List Semantics.FiniteCarrier.Basis)
    (ports : List Semantics.Raw.Port) : Option (List Parameter) := do
  if patterns.length != bases.length || patterns.length != ports.length then none else do
    let bound ← ((patterns.zip bases).zip ports).mapM parameter
    if (bound.map (·.original.binder.text)).Nodup then some bound else none

structure Checked {sources owner name dependencies program}
    (signature : QuantumSignatureCore.Checked sources owner name)
    (root : RuntimeInterval.Prepared dependencies program) where
  patterns : List (List LocatedToken)
  patternsRead : ParameterPatterns.readLocated signature.original = .ok patterns
  entry : List Parameter
  entryRead : parameters patterns signature.inputs program.inputs = some entry
  calls : Adjacent signature.original.occurrence.body

def Checked.parameter {sources owner name dependencies program signature root}
    (checked : @Checked sources owner name dependencies program signature root) (key : String) : Option Parameter :=
  checked.entry.find? (fun entry => entry.original.binder.text == key)

def Checked.lookup {sources owner name dependencies program signature root}
    (checked : @Checked sources owner name dependencies program signature root) (key : String) : Option Owner :=
  (checked.parameter key).map (·.original)

def Checked.naturals {sources owner name dependencies program signature root}
    (_checked : @Checked sources owner name dependencies program signature root) : Semantics.SourceNatural.Names :=
  LexicalNatural.bindingNames signature.staticArguments.naturals

def read {sources owner name dependencies program}
    (signature : QuantumSignatureCore.Checked sources owner name)
    (root : RuntimeInterval.Prepared dependencies program) : WorkM (Checked signature root) := do
  let original := signature.original.occurrence
  exactWork (Exact.charge (64*(original.header.length+original.body.length+program.inputs.length+1)))
  guard (program.classicalInputs.isEmpty && program.effect == .unitary) .request
  match patternsRead : ParameterPatterns.readLocated signature.original with
  | .error _ => throw .request
  | .ok patterns =>
    match entryRead : parameters patterns signature.inputs program.inputs with
    | none => throw .request
    | some entry =>
      let calls ← lift ((readAdjacent original.body).mapError fun _ => .request)
      return ⟨patterns,patternsRead,entry,entryRead,calls⟩

def Checked.wholePorts {sources owner name dependencies program signature root}
    (checked : @Checked sources owner name dependencies program signature root)
    (places : List Place) (ports : List Semantics.Raw.Port) : Bool :=
  (places.zip ports).all fun (place,port) => !place.whole ||
    (checked.parameter place.owner.binder.text).any (fun entry => entry.port == port)

structure First {sources owner name dependencies program signature root}
    (checked : @Checked sources owner name dependencies program signature root)
    (start count : Nat) (inputs outputs : List Nat) where
  interval : RuntimeAccessInterval.Checked checked.calls.before checked.lookup checked.naturals
    (fun _ _ => none) root.block start count inputs outputs
  wholePorts : checked.wholePorts interval.places interval.frame.selected = true

/-- Relate the first written access call to the actual local operations.
Whole owners retain their entry token; an indexed argument still needs the
enclosing extraction evidence. Only literal and bound scalar Nat selectors
are admitted here; helper calls need an original checked interpretation. -/
def readFirst {sources owner name dependencies program signature root}
    (checked : @Checked sources owner name dependencies program signature root)
    (start count : Nat) (inputs outputs : List Nat) : WorkM (First checked start count inputs outputs) := do
  let interval ← RuntimeAccessInterval.read checked.calls.before checked.lookup checked.naturals
    (fun _ _ => none) root.block start count inputs outputs
  if wholePorts : checked.wholePorts interval.places interval.frame.selected = true then
    return ⟨interval,wholePorts⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeAccessSource
