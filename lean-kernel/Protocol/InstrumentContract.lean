import Protocol.Qirf
import QleisliKernel.Qirf.InstrumentContract

/-! Strict observing request data and original expected-artifact bytes.
The native gate reconstructs both graphs; no matrix or success receipt is read.
Decoder/source/native-runtime correspondence remain separate proof obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.InstrumentContract
open Lean Finite Semantics.InstrumentContract

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected instrument fields"

private def number (value : Json) : Except String Nat := do
  let n ← value.getNat?
  if n > 4294967295 then throw "instrument width exceeds u32"
  return n

/-- Decode a complete result tree with bounded intermediate prefix storage.
Ordinary values, quantum owners and every product node remain distinct. -/
def result (fuel : Nat) : Json → Except String (List ResultAtom) :=
  Nat.rec (fun _ => throw "instrument result depth limit") (fun _ recurse value => do
    match ← (← value.getObjVal? "tag").getStr? with
    | "unit" => fields value ["tag"]; pure [.unit]
    | "bit" => fields value ["tag"]; pure [.bit]
    | "bits" =>
      fields value ["tag","width"]
      return [.bits (← number (← value.getObjVal? "width"))]
    | "quantum" =>
      fields value ["tag","basis"]
      return [.quantum (← Qirf.basis 129 (← value.getObjVal? "basis"))]
    | "pair" =>
      fields value ["tag","left","right"]
      let left ← recurse (← value.getObjVal? "left")
      let right ← recurse (← value.getObjVal? "right")
      if left.length + right.length ≥ 4096 then throw "instrument result node limit"
      return .pair :: (left ++ right)
    | "tuple" =>
      fields value ["tag","fields"]
      let values ← (← value.getObjVal? "fields").getArr?
      if values.size < 3 || values.size > 4095 then throw "instrument tuple arity limit"
      let (_,reversed) ← values.toList.foldlM (fun (count,reversed) value => do
        let atoms ← recurse value
        let count := count + atoms.length
        if count ≥ 4096 then throw "instrument result node limit"
        return (count,atoms.reverse ++ reversed)) (0,[])
      return .tuple values.size :: reversed.reverse
    | _ => throw "unknown instrument result") fuel

def signature (value : Json) : Except String Signature := do
  fields value ["input","result"]
  return ⟨← Qirf.basis 129 (← value.getObjVal? "input"),← result 65 (← value.getObjVal? "result")⟩

def identity (value : Json) : Except String Semantics.Function.Identity := do
  fields value ["implementation","specification","sources"]
  let sources ← (← value.getObjVal? "sources").getArr?
  if sources.size > 128 then throw "instrument source count limit"
  let sources ← sources.toList.mapM fun source => do
    fields source ["path","text"]
    return (← (← source.getObjVal? "path").getStr?,← (← source.getObjVal? "text").getStr?)
  return ⟨← (← value.getObjVal? "implementation").getStr?,
    ← (← value.getObjVal? "specification").getStr?,sources⟩

structure Decoded where
  actualSignature : Signature
  expectedSignature : Signature
  identity : Semantics.Function.Identity
  expectedText : String

def decode (value : Json) : Except String Decoded := do
  fields value ["format","version","kind","actual_signature","expected_signature","identity","expected_artifact"]
  let actualSignature ← signature (← value.getObjVal? "actual_signature")
  let expectedSignature ← signature (← value.getObjVal? "expected_signature")
  let identity ← identity (← value.getObjVal? "identity")
  let expectedText ← (← value.getObjVal? "expected_artifact").getStr?
  if expectedText.isEmpty || expectedText.utf8ByteSize > 16777216 then throw "instrument expected artifact byte limit"
  return ⟨actualSignature,expectedSignature,identity,expectedText⟩

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

/-- The actual graph comes from the original QLV1 body. The expected graph is
read from the original UTF-8 string in the same mandatory independent request. -/
def check (actual : QleisliKernel.Qirf.Artifact) (actualOrder : Array Nat)
    (value : Json) : WorkM QleisliKernel.Qirf.InstrumentContract.Checked := do
  let decoded ← adapt (decode value)
  let (expected,expectedOrder) ← Qirf.read decoded.expectedText.toUTF8
  QleisliKernel.Qirf.InstrumentContract.check actual actualOrder expected expectedOrder
    decoded.actualSignature decoded.expectedSignature decoded.identity

structure Acceptance (actual : QleisliKernel.Qirf.Artifact) (actualOrder : Array Nat)
    (value : Json) (checked : QleisliKernel.Qirf.InstrumentContract.Checked) (work left : Nat) where
  decoded : Decoded
  expected : QleisliKernel.Qirf.Artifact
  expectedOrder : Array Nat
  afterExpected : Nat
  requestBound : decode value = .ok decoded
  expectedBound : (Qirf.read decoded.expectedText.toUTF8).run work = (.ok (expected,expectedOrder),afterExpected)
  accepted : (QleisliKernel.Qirf.InstrumentContract.check actual actualOrder expected expectedOrder
    decoded.actualSignature decoded.expectedSignature decoded.identity).run afterExpected = (.ok checked,left)

theorem check_acceptance (actual : QleisliKernel.Qirf.Artifact) (actualOrder : Array Nat)
    (value : Json) (checked : QleisliKernel.Qirf.InstrumentContract.Checked) (work left : Nat)
    (ok : (check actual actualOrder value).run work = (.ok checked,left)) :
    Nonempty (Acceptance actual actualOrder value checked work left) := by
  obtain ⟨decoded,middle,hd,h⟩ := bind_success _ _ _ _ _ ok
  have lifted := lift_success _ _ _ _ hd
  have bound : decode value = .ok decoded := by
    cases definition : decode value <;> simp_all [Except.mapError]
  obtain ⟨⟨expected,expectedOrder⟩,afterExpected,he,hcheck⟩ := bind_success _ _ _ _ _ h
  exact ⟨⟨decoded,expected,expectedOrder,afterExpected,bound,lifted.2 ▸ he,hcheck⟩⟩

end QleisliKernel.Protocol.InstrumentContract
