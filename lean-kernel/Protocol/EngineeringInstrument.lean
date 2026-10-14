import Protocol.Validity
import Protocol.InstrumentContract
import QleisliKernel.Qirf.EngineeringInstrument

/-! Strict engineering-only observing requests and both original artifact bytes.
The unchanged original-root/interface/Kraus checks precede the separate bound;
no exact pair-equality acceptance or producer-supplied matrix is decoded here.
Native/source/runtime preservation and constitutional discharge remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.EngineeringInstrument
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

/-- Fourteen fixed fields bind an engineering instrument comparison only.
Bounds use unsquared norm units. Every majorant is canonical and nonnegative;
the core derives and consumes the complete outcome/cell order independently. -/
def decode (value : Json) : WorkM Decoded := do
  adapt (fields value ["format","version","claim_kind","metric","checker_profile","target_profile",
    "composition","error_category","actual_signature","expected_signature","identity","epsilon",
    "majorants","expected_artifact"])
  let profile ← adapt (do
    return (← (← value.getObjVal? "format").getStr?) == "qleisli.engineering-instrument-request" &&
      (← (← value.getObjVal? "version").getNat?) == 1 &&
      (← (← value.getObjVal? "claim_kind").getStr?) == "engineering-instrument-bound" &&
      (← (← value.getObjVal? "metric").getStr?) == "complete-adjoint-euclidean-operator-norm-v1" &&
      (← (← value.getObjVal? "checker_profile").getStr?) == "choi-l1-r8-instrument-v1" &&
      (← (← value.getObjVal? "target_profile").getStr?) == "qirf-r8-instrument-v1" &&
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

structure Prepared where
  body : ByteArray
  requestBytes : ByteArray
  text : String
  value : Json

def prepare (bytes : ByteArray) : Except String Prepared := do
  let (body,request) ← Validity.packet bytes
  let some request := request | throw "missing engineering request"
  let some text := String.fromUTF8? request | throw "invalid engineering request UTF-8"
  let value ← FiniteCodec.parseWithDepth text 128
  return ⟨body,request,text,value⟩

structure PreparedBinding (bytes : ByteArray) (prepared : Prepared) : Prop where
  packetBound : Validity.packet bytes = .ok (prepared.body,some prepared.requestBytes)
  utf8Bound : String.fromUTF8? prepared.requestBytes = some prepared.text
  parsed : FiniteCodec.parseWithDepth prepared.text 128 = .ok prepared.value

theorem prepare_bound (bytes : ByteArray) (prepared : Prepared)
    (ok : prepare bytes = .ok prepared) : PreparedBinding bytes prepared := by
  unfold prepare at ok
  cases packet : Validity.packet bytes with
  | error error => simp [packet,bind,Except.bind] at ok
  | ok pair =>
    rcases pair with ⟨body,request⟩
    cases request with
    | none => simp [packet,bind,Except.bind] at ok
    | some request =>
      cases utf8 : String.fromUTF8? request with
      | none => simp [packet,utf8,bind,Except.bind] at ok
      | some text =>
        cases parsed : FiniteCodec.parseWithDepth text 128 with
        | error error => simp [packet,utf8,parsed,bind,Except.bind] at ok
        | ok value =>
          simp only [packet,utf8,parsed,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at ok
          subst prepared
          exact ⟨packet,utf8,parsed⟩

structure Retained where
  prepared : Prepared
  actual : QleisliKernel.Qirf.Artifact
  actualOrder : Array Nat
  decoded : Decoded
  expected : QleisliKernel.Qirf.Artifact
  expectedOrder : Array Nat
  checked : QleisliKernel.Qirf.EngineeringInstrument.Checked

/-- The core request contains only the freshly decoded original graphs and
validated typed context. It cannot acquire an exact accepted-program handle. -/
def Retained.request (value : Retained) : QleisliKernel.Qirf.EngineeringInstrument.Request :=
  ⟨value.actual,value.actualOrder,value.expected,value.expectedOrder,
    value.decoded.actualSignature,value.decoded.expectedSignature,value.decoded.identity,
    value.decoded.epsilon,value.decoded.majorants⟩

def checkRetained (bytes : ByteArray) : WorkM Retained := do
  let prepared ← adapt (prepare bytes)
  let (actual,actualOrder) ← Qirf.read prepared.body
  let decoded ← decode prepared.value
  let (expected,expectedOrder) ← Qirf.read decoded.expectedText.toUTF8
  let request : QleisliKernel.Qirf.EngineeringInstrument.Request :=
    ⟨actual,actualOrder,expected,expectedOrder,decoded.actualSignature,decoded.expectedSignature,
      decoded.identity,decoded.epsilon,decoded.majorants⟩
  let checked ← QleisliKernel.Qirf.EngineeringInstrument.check request
  return ⟨prepared,actual,actualOrder,decoded,expected,expectedOrder,checked⟩

structure Binding (bytes : ByteArray) (retained : Retained) (work left : Nat) : Prop where
  prepared : prepare bytes = .ok retained.prepared
  stages : ∃ afterActual afterDecode afterExpected,
    (Qirf.read retained.prepared.body).run work = (.ok (retained.actual,retained.actualOrder),afterActual) ∧
    (decode retained.prepared.value).run afterActual = (.ok retained.decoded,afterDecode) ∧
    (Qirf.read retained.decoded.expectedText.toUTF8).run afterDecode =
      (.ok (retained.expected,retained.expectedOrder),afterExpected) ∧
    (QleisliKernel.Qirf.EngineeringInstrument.check retained.request).run afterExpected = (.ok retained.checked,left)

/-- Every retained field belongs to the actual one-shot request execution.
Neither graph nor the semantic request is chosen by a later existential. -/
theorem checkRetained_bound (bytes : ByteArray) (retained : Retained) (work left : Nat)
    (ok : (checkRetained bytes).run work = (.ok retained,left)) : Binding bytes retained work left := by
  obtain ⟨prepared,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  have lifted := lift_success _ _ _ _ hp
  have preparedBound : prepare bytes = .ok prepared := by
    cases definition : prepare bytes <;> simp_all [adapt,Except.mapError]
  obtain ⟨⟨actual,actualOrder⟩,b,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨decoded,c,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨expected,expectedOrder⟩,d,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,e,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨same,remaining⟩ := pure_success _ _ _ _ h
  subst retained
  subst left
  exact ⟨preparedBound,⟨b,c,d,lifted.2 ▸ ha,hd,hi,hc⟩⟩

end QleisliKernel.Protocol.EngineeringInstrument
