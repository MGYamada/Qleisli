import QleisliKernel.SourceTypes.QuantumMatch

/-! Original exact-label qmatch table and source-function arm headers.
Actual arm/control bodies, source/runtime preservation and native/QDV binding
remain separate obligations. These reads issue no handle or control capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumArms
open Semantics.FiniteCarrier Semantics.Raw Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

structure Label (sources : Sources) where
  ordinal : Nat
  typeQuery : Option (TypeRead sources)

def Label.sourceRows {sources : Sources} (label : @Label sources) : List (String × String) :=
  match label.typeQuery with | none => [] | some query => query.sourceRows

def readLabel (sources : Sources) (caller : String) (selector : Basis) (tokens : List LocatedToken) :
    WorkM (@Label sources) := do
  match selector with
  | [.unit] | [.bit] | [.bits _] =>
    let [literal] := tokens | throw .request
    let ordinal ← adapt (NaturalSyntax.decimal literal.text)
    guard (ordinal ≤ 4294967295) .request
    return ⟨ordinal,none⟩
  | [.enumeration _ variants] =>
    let some variant := tokens.getLast? | throw .request
    guard (tokens.length ≥ 3 && (tokens[tokens.length-2]?.map (·.text)) == some "::") .request
    let ty ← typeExpressionWithSources sources caller ((tokens.dropLast.dropLast).map (·.text))
    guard (ty.basis == selector && variants.contains variant.text) .request
    return ⟨variants.idxOf variant.text,some ty⟩
  | _ => throw .request

structure BoundArm (sources : Sources) (owner : String) (selector target : Basis) where
  written : QuantumMatch.Arm
  label : @Label sources
  originalLabel : ∃ before after,
    (readLabel sources owner selector written.label).run before = (.ok label,after)
  operation : QuantumSignature.Selected sources owner (written.operation.map (·.text))
  input : operation.signature.inputs = [target]
  output : operation.signature.outputs = [target]
  resultOwner : (match operation.signature.parts with | .owner _ => true | .tuple _ => false) = true
  declaredEffect : operation.signature.original.parsedHeader.effect = none ∨
    operation.signature.original.parsedHeader.effect = some .unitary

/-- Header-only module resolution. The enclosing original-body gate must first
check lexical shadowing, including consumed names; this function does not
authorize a source occurrence or replace that persistent-scope check. -/
def readArm (sources : Sources) (owner : String) (selector target : Basis) (written : QuantumMatch.Arm) :
    WorkM (BoundArm sources owner selector target) := do
  let label ← NaturalAffine.witness (readLabel sources owner selector written.label)
  let operation ← QuantumSignature.select sources owner (written.operation.map (·.text))
  if input : operation.signature.inputs = [target] then
    if output : operation.signature.outputs = [target] then
      if shape : (match operation.signature.parts with | .owner _ => true | .tuple _ => false) = true then
        if effect : operation.signature.original.parsedHeader.effect = none ∨
            operation.signature.original.parsedHeader.effect = some .unitary then
          return ⟨written,label.val,by with_reducible exact label.property,operation,input,output,shape,effect⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

def BoundArm.sourceRows {sources owner selector target} (arm : BoundArm sources owner selector target) :
    List (String × String) :=
  arm.label.sourceRows ++ ResolutionProvenance.sourceRows arm.operation.resolution ++
    arm.operation.signature.sourceRows

/-- A public observing/isometric declaration cannot be relabeled by the
enclosing source-arm query. Private inference still requires actual body checks. -/
theorem BoundArm.publicUnitary {sources owner selector target}
    (arm : BoundArm sources owner selector target)
    (isPublic : arm.operation.signature.original.declaration.isPublic = true) :
    arm.operation.signature.original.parsedHeader.effect = some .unitary := by
  have present := arm.operation.signature.publicEffect isPublic
  rcases arm.declaredEffect with absent | exactEffect
  · simp [absent] at present
  · exact exactEffect

def partition {sources owner selector target} (count : Nat) (arms : List (BoundArm sources owner selector target)) : Bool :=
  let labels := arms.map (·.label.ordinal)
  labels.length == count && labels.all (· < count) && labels.eraseDups.length == labels.length

/-- Original arm headers and label coverage, not an enclosing lexical-scope
judgment. Current native admission also requires QuantumSequence.read. -/
structure Table (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) where
  site : QuantumMatch.Site sources owner name offset
  layout : Semantics.FiniteCarrier.Layout
  originalTypes : ∃ before after, (SourceTypes.checkMany sources [selector,target]).run before = (.ok (),after)
  selectorLayout : Semantics.FiniteCarrier.layout selector = some layout
  arms : List (BoundArm sources owner selector target)
  originalArms : arms.map (·.written) = site.parsed.arms
  complete : partition layout.labels.length arms = true

def read (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) :
    WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.read sources owner name offset
  let original ← NaturalAffine.witness (SourceTypes.checkMany sources [selector,target])
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let arms ← site.parsed.arms.mapM (readArm sources owner selector target)
  exactWork (Exact.charge (256*(site.parsed.tokens.length+1)*(arms.length+1)))
  if same : arms.map (·.written) = site.parsed.arms then
    if complete : partition layout.val.labels.length arms = true then
      return ⟨site,layout.val,by with_reducible exact original.property,
        by obtain ⟨before,after,ran⟩ := layout.property
           exact FiniteCarrier.read_reference _ _ _ _ ran,
        arms,same,complete⟩
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.QuantumArms
