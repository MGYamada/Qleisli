import Protocol.Carrier
import QleisliKernel.Qirf.SourceFrameSector

/-! Strict version-paired transport for the internal named-arm source component.
Existing carrier syntax, QIRF decoding and fresh source/arm checking are reused.
This adapter has no dispatcher or accepted-handle constructor of its own.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.Qmatch
open Lean Finite Semantics.CarrierInterface

def profile := "finite-source-qmatch-named-v2"

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

private def field (value : Json) (key : String) := value.getObjVal? key
private def text (value : Json) := value.getStr?
private def number (value : Json) : Except String Nat := do
  let value ← value.getNat?
  if value > 4294967295 then throw "qmatch index exceeds u32"
  return value

structure SourceSite where
  moduleName : String
  functionName : String
  offset : Nat
  deriving BEq, DecidableEq, Repr

private def sourceSite (value : Json) : Except String SourceSite := do
  Carrier.fields value ["module","function","offset"]
  let moduleName ← text (← field value "module")
  let functionName ← text (← field value "function")
  if moduleName.isEmpty || functionName.isEmpty || moduleName.utf8ByteSize > 4096 || functionName.utf8ByteSize > 4096 then
    throw "qmatch source name capacity"
  return ⟨moduleName,functionName,← number (← field value "offset")⟩

private def arm (value : Json) : Except String Qirf.SourceArm.Programs := do
  Carrier.fields value ["evidence","controlled"]
  return ⟨← number (← field value "evidence"),← number (← field value "controlled")⟩

structure Request where
  attached : Interface
  required : Interface
  source : SourceSite
  arms : List Qirf.SourceArm.Programs

def decode (value : Json) : WorkM Request := do
  adapt (Carrier.fields value ["format","version","profile","attached","required","source","arms"])
  let supported ← adapt (do
    return (← text (← field value "format")) == "qleisli.qmatch-request" &&
      (← number (← field value "version")) == 2 && (← text (← field value "profile")) == profile)
  guard supported .request
  let attached ← adapt (Carrier.readInterface (← adapt (field value "attached")))
  let required ← adapt (Carrier.readInterface (← adapt (field value "required")))
  let source ← adapt (sourceSite (← adapt (field value "source")))
  let arms ← adapt ((← adapt (field value "arms")).getArr?)
  guard (0 < arms.size && arms.size ≤ 64) .limit
  let arms ← adapt (arms.toList.mapM arm)
  return ⟨attached,required,source,arms⟩

def readRequest (bytes : ByteArray) : WorkM Request := do
  let value ← adapt (do
    let some text := String.fromUTF8? bytes | throw "invalid qmatch request UTF-8"
    FiniteCodec.parseWithDepth text 128)
  decode value

structure Checked where
  body : ByteArray
  requestBytes : ByteArray
  artifact : Qirf.Artifact
  order : Array Nat
  request : Request
  result : Qirf.SourceFrameSector.Checked artifact order request.attached request.required
    request.source.moduleName request.source.functionName request.source.offset request.arms

def check (bytes : ByteArray) : WorkM Checked := do
  let (body,requested) ← adapt (Validity.packet bytes)
  let some requestBytes := requested | throw .request
  let (artifact,order) ← Protocol.Qirf.readAll body
  let request ← readRequest requestBytes
  let result ← Qirf.SourceFrameSector.check artifact order request.attached request.required
    request.source.moduleName request.source.functionName request.source.offset request.arms
  return ⟨body,requestBytes,artifact,order,request,result⟩

structure Binding (bytes : ByteArray) (checked : Checked) (work left : Nat) : Prop where
  packet : Validity.packet bytes = .ok (checked.body,some checked.requestBytes)
  artifact : ∃ a b, (Protocol.Qirf.readAll checked.body).run a = (.ok (checked.artifact,checked.order),b)
  request : ∃ a b, (readRequest checked.requestBytes).run a = (.ok checked.request,b)
  core : ∃ a, (Qirf.SourceFrameSector.check checked.artifact checked.order checked.request.attached
    checked.request.required checked.request.source.moduleName checked.request.source.functionName
    checked.request.source.offset checked.request.arms).run a = (.ok checked.result,left)

theorem check_binding (bytes : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes).run work = (.ok checked,left)) : Binding bytes checked work left := by
  unfold check at ok
  obtain ⟨packet,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  cases requested : packet.2 with
  | none => simp only [requested] at h; cases h
  | some requestBytes =>
    simp only [requested] at h
    obtain ⟨decoded,b,ha,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨request,c,hr,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨result,d,hc,h⟩ := bind_success _ _ _ _ _ h
    have final := (pure_success _ _ _ _ h)
    rcases final with ⟨rfl,rfl⟩
    have parsed := (lift_success _ _ _ _ hp).1
    have packetBound : Validity.packet bytes = .ok packet := by
      cases value : Validity.packet bytes <;> simp_all [Except.mapError]
    refine ⟨?_,⟨a,b,ha⟩,⟨b,c,hr⟩,⟨c,hc⟩⟩
    exact packetBound.trans (congrArg Except.ok (Prod.ext rfl requested))

end QleisliKernel.Protocol.Qmatch
