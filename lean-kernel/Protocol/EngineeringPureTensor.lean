import Protocol.EngineeringPure
import QleisliKernel.Qirf.EngineeringPureTensor

/-! A separate engineering adapter for exactly two ordered pure components.
Every original graph is decoded afresh; the actual checker shares one work
state across six original roots, both parent equations and literal budgets.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.EngineeringPureTensor
open Lean Finite Semantics.Exact

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected tensor fields"

private def port (value : Json) : Except String Semantics.Raw.Port := do
  fields value ["token","wires","shape"]
  let shape ← value.getObjVal? "shape"
  fields shape ["bits"]
  return ⟨← (← value.getObjVal? "token").getNat?,
    ← (← (← value.getObjVal? "wires").getArr?).toList.mapM Json.getNat?,
    ← (← shape.getObjVal? "bits").getNat?⟩

private def leaf (value : Json) : WorkM EngineeringPure.Leaf := do
  adapt (fields value ["input","output","matrix"])
  let input ← adapt (port (← adapt (value.getObjVal? "input")))
  let output ← adapt (port (← adapt (value.getObjVal? "output")))
  let required ← FiniteCodec.readMatrixValue (← adapt (value.getObjVal? "matrix"))
  return ⟨input,output,required⟩

private def budget (value : Json) : WorkM Coefficient := do
  adapt (fields value ["numerator","denominator_bits"])
  let numerator ← adapt ((← adapt (value.getObjVal? "numerator")).getStr?)
  let exponent ← adapt ((← adapt (value.getObjVal? "denominator_bits")).getNat?)
  let result ← lift (dyadicRead ⟨numerator,exponent⟩)
  guard (result.numerator ≥ 0) .request
  return result

private def original (value : Json) : WorkM String := do
  let text ← adapt value.getStr?
  guard (!text.isEmpty && text.utf8ByteSize ≤ Validity.maxFileBytes) .limit
  return text

structure Component where
  domain : Semantics.Finite.Basis
  codomain : Semantics.Finite.Basis
  actual : EngineeringPure.Leaf
  ideal : EngineeringPure.Leaf
  epsilon : Coefficient
  actualText : String
  idealText : String

private def component (value : Json) : WorkM Component := do
  adapt (fields value ["domain","codomain","actual","ideal","epsilon",
    "actual_artifact","expected_artifact"])
  let domain ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "domain")))
  let codomain ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "codomain")))
  let actual ← leaf (← adapt (value.getObjVal? "actual"))
  let ideal ← leaf (← adapt (value.getObjVal? "ideal"))
  let epsilon ← budget (← adapt (value.getObjVal? "epsilon"))
  let actualText ← original (← adapt (value.getObjVal? "actual_artifact"))
  let idealText ← original (← adapt (value.getObjVal? "expected_artifact"))
  return ⟨domain,codomain,actual,ideal,epsilon,actualText,idealText⟩

structure Decoded where
  actual : EngineeringPure.Leaf
  ideal : EngineeringPure.Leaf
  epsilon : Coefficient
  left : Component
  right : Component
  expectedText : String

def Decoded.domain (value : Decoded) : Semantics.Finite.Basis :=
  Semantics.Finite.Basis.pair value.left.domain value.right.domain

def Decoded.codomain (value : Decoded) : Semantics.Finite.Basis :=
  Semantics.Finite.Basis.pair value.left.codomain value.right.codomain

/-- Only this fixed two-component tensor profile is decoded. The literal
parent budget is checked against exact addition by the core, never relaxed. -/
def decode (value : Json) : WorkM Decoded := do
  adapt (fields value ["format","version","claim_kind","metric","checker_profile","target_profile",
    "composition","error_category","actual","ideal","epsilon","left","right","expected_artifact"])
  let profile ← adapt (do
    return (← (← value.getObjVal? "format").getStr?) == "qleisli.engineering-pure-tensor-request" &&
      (← (← value.getObjVal? "version").getNat?) == 1 &&
      (← (← value.getObjVal? "claim_kind").getStr?) == "engineering-pure-tensor-bound" &&
      (← (← value.getObjVal? "metric").getStr?) == "pure-euclidean-operator-norm-v1" &&
      (← (← value.getObjVal? "checker_profile").getStr?) == "tensor-additive-r8-pure-leaf-v1" &&
      (← (← value.getObjVal? "target_profile").getStr?) == "qirf-r8-pure-v1" &&
      (← (← value.getObjVal? "composition").getStr?) == "ordered-tensor-two-v1" &&
      (← (← value.getObjVal? "error_category").getStr?) == "implementation-distance")
  guard profile .request
  let actual ← leaf (← adapt (value.getObjVal? "actual"))
  let ideal ← leaf (← adapt (value.getObjVal? "ideal"))
  let epsilon ← budget (← adapt (value.getObjVal? "epsilon"))
  let left ← component (← adapt (value.getObjVal? "left"))
  let right ← component (← adapt (value.getObjVal? "right"))
  let expectedText ← original (← adapt (value.getObjVal? "expected_artifact"))
  return ⟨actual,ideal,epsilon,left,right,expectedText⟩

abbrev Prepared := EngineeringPure.Prepared
abbrev PreparedBinding := EngineeringPure.PreparedBinding
abbrev prepare := EngineeringPure.prepare

structure Retained where
  prepared : Prepared
  actual : QleisliKernel.Qirf.Artifact
  actualOrder : Array Nat
  decoded : Decoded
  ideal : QleisliKernel.Qirf.Artifact
  idealOrder : Array Nat
  leftActual : QleisliKernel.Qirf.Artifact
  leftActualOrder : Array Nat
  leftIdeal : QleisliKernel.Qirf.Artifact
  leftIdealOrder : Array Nat
  rightActual : QleisliKernel.Qirf.Artifact
  rightActualOrder : Array Nat
  rightIdeal : QleisliKernel.Qirf.Artifact
  rightIdealOrder : Array Nat
  checked : QleisliKernel.Qirf.EngineeringPureTensor.Checked

private def componentRequest (value : Component)
    (actual : QleisliKernel.Qirf.Artifact) (actualOrder : Array Nat)
    (ideal : QleisliKernel.Qirf.Artifact) (idealOrder : Array Nat) :
    QleisliKernel.Qirf.EngineeringPure.Request :=
  ⟨value.domain,value.codomain,
    ⟨actual,actualOrder,value.actual.input,value.actual.output,value.actual.required⟩,
    ⟨ideal,idealOrder,value.ideal.input,value.ideal.output,value.ideal.required⟩,value.epsilon⟩

/-- This request is constructed from all six freshly decoded retained graphs
and the complete typed request, rather than producer receipts or matrices alone. -/
def Retained.request (value : Retained) : QleisliKernel.Qirf.EngineeringPureTensor.Request :=
  ⟨componentRequest value.decoded.left value.leftActual value.leftActualOrder
      value.leftIdeal value.leftIdealOrder,
    componentRequest value.decoded.right value.rightActual value.rightActualOrder
      value.rightIdeal value.rightIdealOrder,
    ⟨value.actual,value.actualOrder,value.decoded.actual.input,value.decoded.actual.output,
      value.decoded.actual.required⟩,
    ⟨value.ideal,value.idealOrder,value.decoded.ideal.input,value.decoded.ideal.output,
      value.decoded.ideal.required⟩,value.decoded.epsilon⟩

def checkRetained (bytes : ByteArray) : WorkM Retained := do
  let prepared ← adapt (prepare bytes)
  let (actual,actualOrder) ← Qirf.read prepared.body
  let decoded ← decode prepared.value
  let (ideal,idealOrder) ← Qirf.read decoded.expectedText.toUTF8
  let (leftActual,leftActualOrder) ← Qirf.read decoded.left.actualText.toUTF8
  let (leftIdeal,leftIdealOrder) ← Qirf.read decoded.left.idealText.toUTF8
  let (rightActual,rightActualOrder) ← Qirf.read decoded.right.actualText.toUTF8
  let (rightIdeal,rightIdealOrder) ← Qirf.read decoded.right.idealText.toUTF8
  let request : QleisliKernel.Qirf.EngineeringPureTensor.Request :=
    ⟨componentRequest decoded.left leftActual leftActualOrder leftIdeal leftIdealOrder,
      componentRequest decoded.right rightActual rightActualOrder rightIdeal rightIdealOrder,
      ⟨actual,actualOrder,decoded.actual.input,decoded.actual.output,decoded.actual.required⟩,
      ⟨ideal,idealOrder,decoded.ideal.input,decoded.ideal.output,decoded.ideal.required⟩,decoded.epsilon⟩
  let checked ← QleisliKernel.Qirf.EngineeringPureTensor.check request
  return ⟨prepared,actual,actualOrder,decoded,ideal,idealOrder,leftActual,leftActualOrder,
    leftIdeal,leftIdealOrder,rightActual,rightActualOrder,rightIdeal,rightIdealOrder,checked⟩

structure Binding (bytes : ByteArray) (retained : Retained) (work left : Nat) : Prop where
  prepared : prepare bytes = .ok retained.prepared
  stages : ∃ afterActual afterDecode afterIdeal afterLeftActual afterLeftIdeal afterRightActual afterRightIdeal,
    (Qirf.read retained.prepared.body).run work = (.ok (retained.actual,retained.actualOrder),afterActual) ∧
    (decode retained.prepared.value).run afterActual = (.ok retained.decoded,afterDecode) ∧
    (Qirf.read retained.decoded.expectedText.toUTF8).run afterDecode =
      (.ok (retained.ideal,retained.idealOrder),afterIdeal) ∧
    (Qirf.read retained.decoded.left.actualText.toUTF8).run afterIdeal =
      (.ok (retained.leftActual,retained.leftActualOrder),afterLeftActual) ∧
    (Qirf.read retained.decoded.left.idealText.toUTF8).run afterLeftActual =
      (.ok (retained.leftIdeal,retained.leftIdealOrder),afterLeftIdeal) ∧
    (Qirf.read retained.decoded.right.actualText.toUTF8).run afterLeftIdeal =
      (.ok (retained.rightActual,retained.rightActualOrder),afterRightActual) ∧
    (Qirf.read retained.decoded.right.idealText.toUTF8).run afterRightActual =
      (.ok (retained.rightIdeal,retained.rightIdealOrder),afterRightIdeal) ∧
    (QleisliKernel.Qirf.EngineeringPureTensor.check retained.request).run afterRightIdeal =
      (.ok retained.checked,left)

/-- Successful transport is linked to the actual sequence of all six original
reads and the subsequent composed checker on precisely those retained objects. -/
theorem checkRetained_bound (bytes : ByteArray) (retained : Retained) (work left : Nat)
    (ok : (checkRetained bytes).run work = (.ok retained,left)) : Binding bytes retained work left := by
  obtain ⟨prepared,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  have lifted := lift_success _ _ _ _ hp
  have preparedBound : prepare bytes = .ok prepared := by
    cases definition : prepare bytes <;> simp_all [adapt,Except.mapError]
  obtain ⟨⟨actual,actualOrder⟩,b,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨decoded,c,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨ideal,idealOrder⟩,d,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨leftActual,leftActualOrder⟩,e,hla,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨leftIdeal,leftIdealOrder⟩,f,hli,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨rightActual,rightActualOrder⟩,g,hra,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨⟨rightIdeal,rightIdealOrder⟩,j,hri,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,k,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨same,remaining⟩ := pure_success _ _ _ _ h
  subst retained
  subst left
  exact ⟨preparedBound,⟨b,c,d,e,f,g,j,lifted.2 ▸ ha,hd,hi,hla,hli,hra,hri,hc⟩⟩

end QleisliKernel.Protocol.EngineeringPureTensor
