import Protocol.Validity
import Protocol.InstrumentContract
import QleisliKernel.Qirf.EngineeringOpenQasm
import Protocol.EngineeringInstrument

/-! Strict engineering-only target requests and the original ideal artifact bytes.
The unchanged original-root/interface/Kraus checks precede the separate bound;
no exact pair-equality acceptance or producer-supplied matrix is decoded here.
Native/source/runtime preservation and constitutional discharge remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.EngineeringOpenQasm
open Lean Finite Semantics.Exact

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected engineering instrument fields"

private def bound (value : Json) : WorkM Coefficient := do
  adapt (fields value ["numerator","denominator_bits"])
  let numerator ← adapt ((← adapt (value.getObjVal? "numerator")).getStr?)
  let exponent ← adapt ((← adapt (value.getObjVal? "denominator_bits")).getNat?)
  let result ← lift (dyadicRead ⟨numerator,exponent⟩)
  guard (result.numerator ≥ 0) .request
  return result

structure Decoded where
  actualSignature : Semantics.InstrumentContract.Signature
  expectedSignature : Semantics.InstrumentContract.Signature
  identity : Semantics.Function.Identity
  epsilon : Coefficient
  majorants : List Coefficient
  expectedText : String

/-- Fourteen fixed fields bind the canonical target engineering profile only.
Bounds use unsquared norm units. Every majorant is canonical and nonnegative;
the core derives and consumes the complete outcome/cell order independently. -/
def decode (value : Json) : WorkM Decoded := do
  adapt (fields value ["format","version","claim_kind","metric","checker_profile","target_profile",
    "composition","error_category","actual_signature","expected_signature","identity","epsilon",
    "majorants","expected_artifact"])
  let profile ← adapt (do
    return (← (← value.getObjVal? "format").getStr?) == "qleisli.engineering-openqasm-request" &&
      (← (← value.getObjVal? "version").getNat?) == 1 &&
      (← (← value.getObjVal? "claim_kind").getStr?) == "engineering-target-instrument-bound" &&
      (← (← value.getObjVal? "metric").getStr?) == "complete-adjoint-euclidean-operator-norm-v1" &&
      (← (← value.getObjVal? "checker_profile").getStr?) == "canonical-target-choi-l1-r8-v1" &&
      (← (← value.getObjVal? "target_profile").getStr?) == "openqasm3-canonical-one-qubit-terminal-r8-v1" &&
      (← (← value.getObjVal? "composition").getStr?) == "single-component-v1" &&
      (← (← value.getObjVal? "error_category").getStr?) == "implementation-distance")
  guard profile .request
  let actualSignature ← adapt (InstrumentContract.signature (← adapt (value.getObjVal? "actual_signature")))
  let expectedSignature ← adapt (InstrumentContract.signature (← adapt (value.getObjVal? "expected_signature")))
  let identity ← adapt (InstrumentContract.identity (← adapt (value.getObjVal? "identity")))
  let epsilon ← bound (← adapt (value.getObjVal? "epsilon"))
  let majorantValues ← adapt ((← adapt (value.getObjVal? "majorants")).getArr?)
  -- Charge before converting/traversing the witness array, in the same work
  -- state later used for both graph reconstructions and every coefficient.
  exactWork (Exact.charge majorantValues.size)
  let majorants ← majorantValues.toList.mapM bound
  let expectedText ← adapt ((← adapt (value.getObjVal? "expected_artifact")).getStr?)
  guard (!expectedText.isEmpty && expectedText.utf8ByteSize ≤ Validity.maxFileBytes) .limit
  return ⟨actualSignature,expectedSignature,identity,epsilon,majorants,expectedText⟩

abbrev Prepared := EngineeringInstrument.Prepared
abbrev PreparedBinding := EngineeringInstrument.PreparedBinding
abbrev prepare := EngineeringInstrument.prepare

structure Retained where
  prepared : Prepared
  decoded : Decoded
  expected : QleisliKernel.Qirf.Artifact
  expectedOrder : Array Nat
  checked : QleisliKernel.Qirf.EngineeringOpenQasm.Checked

/-- The actual target is the original inner body bytes; the ideal and its full
indexed dependency graph are freshly decoded, never supplied as a receipt. -/
def Retained.request (value : Retained) : QleisliKernel.Qirf.EngineeringOpenQasm.Request :=
  ⟨value.prepared.body,value.expected,value.expectedOrder,
    value.decoded.actualSignature,value.decoded.expectedSignature,value.decoded.identity,
    value.decoded.epsilon,value.decoded.majorants⟩

def checkRetained (bytes : ByteArray) : WorkM Retained := do
  let prepared ← adapt (prepare bytes)
  let decoded ← decode prepared.value
  let (expected,expectedOrder) ← Qirf.read decoded.expectedText.toUTF8
  let request : QleisliKernel.Qirf.EngineeringOpenQasm.Request :=
    ⟨prepared.body,expected,expectedOrder,decoded.actualSignature,decoded.expectedSignature,
      decoded.identity,decoded.epsilon,decoded.majorants⟩
  let checked ← QleisliKernel.Qirf.EngineeringOpenQasm.check request
  return ⟨prepared,decoded,expected,expectedOrder,checked⟩

structure Binding (bytes : ByteArray) (retained : Retained) (work left : Nat) : Prop where
  prepared : prepare bytes = .ok retained.prepared
  stages : ∃ afterDecode afterExpected,
    (decode retained.prepared.value).run work = (.ok retained.decoded,afterDecode) ∧
    (Qirf.read retained.decoded.expectedText.toUTF8).run afterDecode =
      (.ok (retained.expected,retained.expectedOrder),afterExpected) ∧
    (QleisliKernel.Qirf.EngineeringOpenQasm.check retained.request).run afterExpected =
      (.ok retained.checked,left)

/-- All retained fields belong to the actual one-shot target request execution;
the full original ideal read and target checker share the remaining work. -/
theorem checkRetained_bound (bytes : ByteArray) (retained : Retained) (work left : Nat)
    (ok : (checkRetained bytes).run work = (.ok retained,left)) : Binding bytes retained work left := by
  obtain ⟨prepared,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  have lifted := lift_success _ _ _ _ hp
  have preparedBound : prepare bytes = .ok prepared := by
    cases definition : prepare bytes <;> simp_all [adapt,Except.mapError]
  obtain ⟨decoded,b,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨expected,expectedOrder⟩,c,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,d,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨same,remaining⟩ := pure_success _ _ _ _ h
  subst retained
  subst left
  exact ⟨preparedBound,⟨b,c,lifted.2 ▸ hd,he,hc⟩⟩

end QleisliKernel.Protocol.EngineeringOpenQasm
