import Protocol.Validity
import QleisliKernel.Qirf.EngineeringPure

/-! A private engineering request adapter, separate from exact native contracts.
Original actual and ideal artifacts are decoded afresh before the unchanged
pure-leaf gates and the engineering inequality run with one work state.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.EngineeringPure
open Lean Finite Semantics.Exact

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected engineering fields"

private def port (value : Json) : Except String Semantics.Raw.Port := do
  fields value ["token","wires","shape"]
  let shape ← value.getObjVal? "shape"
  fields shape ["bits"]
  return ⟨← (← value.getObjVal? "token").getNat?,
    ← (← (← value.getObjVal? "wires").getArr?).toList.mapM Json.getNat?,
    ← (← shape.getObjVal? "bits").getNat?⟩

structure Leaf where
  input : Semantics.Raw.Port
  output : Semantics.Raw.Port
  required : Matrix

private def leaf (value : Json) : WorkM Leaf := do
  adapt (fields value ["input","output","matrix"])
  let input ← adapt (port (← adapt (value.getObjVal? "input")))
  let output ← adapt (port (← adapt (value.getObjVal? "output")))
  let required ← FiniteCodec.readMatrixValue (← adapt (value.getObjVal? "matrix"))
  return ⟨input,output,required⟩

structure Decoded where
  domain : Semantics.Finite.Basis
  codomain : Semantics.Finite.Basis
  actual : Leaf
  ideal : Leaf
  epsilon : Coefficient
  expectedText : String

/-- Only the fixed single-component, pure, phase-sensitive engineering profile
is decoded. Unknown fields, noncanonical budgets and alternate profiles fail. -/
def decode (value : Json) : WorkM Decoded := do
  adapt (fields value ["format","version","claim_kind","metric","checker_profile","target_profile",
    "composition","error_category","domain","codomain","actual","ideal","epsilon","expected_artifact"])
  let profile ← adapt (do
    return (← (← value.getObjVal? "format").getStr?) == "qleisli.engineering-pure-request" &&
      (← (← value.getObjVal? "version").getNat?) == 1 &&
      (← (← value.getObjVal? "claim_kind").getStr?) == "engineering" &&
      (← (← value.getObjVal? "metric").getStr?) == "pure-euclidean-operator-norm-v1" &&
      (← (← value.getObjVal? "checker_profile").getStr?) == "frobenius-r8-pure-leaf-v1" &&
      (← (← value.getObjVal? "target_profile").getStr?) == "qirf-r8-pure-v1" &&
      (← (← value.getObjVal? "composition").getStr?) == "single-component-v1" &&
      (← (← value.getObjVal? "error_category").getStr?) == "implementation-distance")
  guard profile .request
  let domain ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "domain")))
  let codomain ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "codomain")))
  let actual ← leaf (← adapt (value.getObjVal? "actual"))
  let ideal ← leaf (← adapt (value.getObjVal? "ideal"))
  let epsilonValue ← adapt (value.getObjVal? "epsilon")
  adapt (fields epsilonValue ["numerator","denominator_bits"])
  let numerator ← adapt ((← adapt (epsilonValue.getObjVal? "numerator")).getStr?)
  let exponent ← adapt ((← adapt (epsilonValue.getObjVal? "denominator_bits")).getNat?)
  let epsilon ← lift (dyadicRead ⟨numerator,exponent⟩)
  guard (epsilon.numerator ≥ 0) .request
  let expectedText ← adapt ((← adapt (value.getObjVal? "expected_artifact")).getStr?)
  guard (!expectedText.isEmpty && expectedText.utf8ByteSize ≤ Validity.maxFileBytes) .limit
  return ⟨domain,codomain,actual,ideal,epsilon,expectedText⟩

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
  ideal : QleisliKernel.Qirf.Artifact
  idealOrder : Array Nat
  checked : QleisliKernel.Qirf.EngineeringPure.Checked

/-- The exact request to the engineering core is constructed only from freshly
decoded original artifacts and retained typed request fields. -/
def Retained.request (value : Retained) : QleisliKernel.Qirf.EngineeringPure.Request :=
  ⟨value.decoded.domain,value.decoded.codomain,
    ⟨value.actual,value.actualOrder,value.decoded.actual.input,value.decoded.actual.output,
      value.decoded.actual.required⟩,
    ⟨value.ideal,value.idealOrder,value.decoded.ideal.input,value.decoded.ideal.output,
      value.decoded.ideal.required⟩,value.decoded.epsilon⟩

def checkRetained (bytes : ByteArray) : WorkM Retained := do
  let prepared ← adapt (prepare bytes)
  let (actual,actualOrder) ← Qirf.read prepared.body
  let decoded ← decode prepared.value
  let (ideal,idealOrder) ← Qirf.read decoded.expectedText.toUTF8
  let request : QleisliKernel.Qirf.EngineeringPure.Request :=
    ⟨decoded.domain,decoded.codomain,
      ⟨actual,actualOrder,decoded.actual.input,decoded.actual.output,decoded.actual.required⟩,
      ⟨ideal,idealOrder,decoded.ideal.input,decoded.ideal.output,decoded.ideal.required⟩,decoded.epsilon⟩
  let checked ← QleisliKernel.Qirf.EngineeringPure.check request
  return ⟨prepared,actual,actualOrder,decoded,ideal,idealOrder,checked⟩

structure Binding (bytes : ByteArray) (retained : Retained) (work left : Nat) : Prop where
  prepared : prepare bytes = .ok retained.prepared
  stages : ∃ afterActual afterDecode afterIdeal,
    (Qirf.read retained.prepared.body).run work = (.ok (retained.actual,retained.actualOrder),afterActual) ∧
    (decode retained.prepared.value).run afterActual = (.ok retained.decoded,afterDecode) ∧
    (Qirf.read retained.decoded.expectedText.toUTF8).run afterDecode =
      (.ok (retained.ideal,retained.idealOrder),afterIdeal) ∧
    (QleisliKernel.Qirf.EngineeringPure.check retained.request).run afterIdeal = (.ok retained.checked,left)

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
  obtain ⟨⟨ideal,idealOrder⟩,d,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,e,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨same,remaining⟩ := pure_success _ _ _ _ h
  subst retained
  subst left
  exact ⟨preparedBound,⟨b,c,d,lifted.2 ▸ ha,hd,hi,hc⟩⟩

end QleisliKernel.Protocol.EngineeringPure
