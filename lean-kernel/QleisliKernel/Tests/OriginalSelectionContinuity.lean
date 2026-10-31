import QleisliKernel.SourceTypes.QuantumArms

/-! Frozen reader algorithms before shared original-witness extraction.
No runtime checker imports these test-only baselines.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.OriginalSelectionContinuity
open QleisliKernel QleisliKernel.SourceTypes
open Finite Semantics.FiniteCarrier
open QuantumMatch QuantumArms

def legacySite (sources : Sources) (owner name : String) (offset : Nat) :
    WorkM (Site sources owner name offset) := do
  let original ← OrdinarySignature.readOriginal sources owner name
  let body := original.occurrence.body
  exactWork (Exact.charge (256*(body.length+1)))
  let leading := body.takeWhile (fun token => token.span.startByte != offset)
  match parsed : parse (body.drop leading.length) with
  | .error _ => throw .request
  | .ok (site,suffix) =>
    if same : body = leading ++ site.tokens ++ suffix ∧ site.keyword.span.startByte = offset then
      return ⟨original,site,leading,suffix,same.1,same.2,parsed⟩
    else throw .request

def legacyArms (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) :
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

theorem siteWrapper (sources : Sources) (owner name : String) (offset : Nat) :
    QuantumMatch.read sources owner name offset = legacySite sources owner name offset := by
  rfl

theorem armsWrapper (sources : Sources) (owner name : String)
    (offset : Nat) (selector target : Basis) :
    QuantumArms.read sources owner name offset selector target =
      legacyArms sources owner name offset selector target := by
  simp only [QuantumArms.read, QuantumArms.readArms, legacyArms, QuantumMatch.read, bind_assoc]

end QleisliKernel.Tests.OriginalSelectionContinuity
