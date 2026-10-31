import Protocol.Carrier
import QleisliKernel.Qirf.ContextSector

/-! Strict version-paired transport for complete original source contexts.
Existing carrier syntax, QIRF decoding and fresh source/arm checking are reused.
This adapter has no dispatcher or accepted-handle constructor of its own.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.Qmatch
open Lean Finite Semantics.CarrierInterface

def profile := "finite-source-qmatch-context-v4"

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
  deriving BEq, DecidableEq, Repr

private def sourceSite (value : Json) : Except String SourceSite := do
  Carrier.fields value ["module","function"]
  let moduleName ← text (← field value "module")
  let functionName ← text (← field value "function")
  if moduleName.isEmpty || functionName.isEmpty || moduleName.utf8ByteSize > 4096 || functionName.utf8ByteSize > 4096 then
    throw "qmatch source name capacity"
  return ⟨moduleName,functionName⟩

private def arm (value : Json) : Except String Qirf.SourceArm.Programs := do
  Carrier.fields value ["evidence","controlled"]
  return ⟨← number (← field value "evidence"),← number (← field value "controlled")⟩

structure Request where
  source : SourceSite
  positions : List Qirf.SourceSequence.Position
  sites : List Qirf.SelectionContract.Request

private def position (value : Json) : Except String Qirf.SourceSequence.Position := do
  Carrier.fields value ["offset","start","count"]
  return ⟨← number (← field value "offset"),← number (← field value "start"),← number (← field value "count")⟩

private def site (value : Json) : WorkM Qirf.SelectionContract.Request := do
  adapt (Carrier.fields value ["attached","required","position","arms"])
  let attached ← adapt (Carrier.readInterface (← adapt (field value "attached")))
  let required ← adapt (Carrier.readInterface (← adapt (field value "required")))
  let location ← adapt (position (← adapt (field value "position")))
  let arms ← adapt ((← adapt (field value "arms")).getArr?)
  guard (0 < arms.size && arms.size ≤ 64) .limit
  return ⟨attached,required,location,← adapt (arms.toList.mapM arm)⟩

def decode (value : Json) : WorkM Request := do
  adapt (Carrier.fields value ["format","version","profile","source","positions","sites"])
  let supported ← adapt (do
    return (← text (← field value "format")) == "qleisli.qmatch-request" &&
      (← number (← field value "version")) == 4 && (← text (← field value "profile")) == profile)
  guard supported .request
  let source ← adapt (sourceSite (← adapt (field value "source")))
  let positions ← adapt ((← adapt (field value "positions")).getArr?)
  exactWork (Exact.charge (8*(positions.size+1)))
  let positions ← adapt (positions.toList.mapM position)
  let sites ← adapt ((← adapt (field value "sites")).getArr?)
  guard (0 < sites.size && sites.size ≤ 128) .limit
  return ⟨source,positions,← sites.toList.mapM site⟩

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
  result : Qirf.ContextSector.Checked artifact order request.source.moduleName request.source.functionName
    request.positions request.sites

def check (bytes : ByteArray) : WorkM Checked := do
  let (body,requested) ← adapt (Validity.packet bytes)
  let some requestBytes := requested | throw .request
  let (artifact,order) ← Protocol.Qirf.readAll body
  let request ← readRequest requestBytes
  let result ← Qirf.ContextSector.check artifact order request.source.moduleName request.source.functionName
    request.positions request.sites
  return ⟨body,requestBytes,artifact,order,request,result⟩

structure Binding (bytes : ByteArray) (checked : Checked) (work left : Nat) : Prop where
  packet : Validity.packet bytes = .ok (checked.body,some checked.requestBytes)
  artifact : ∃ a b, (Protocol.Qirf.readAll checked.body).run a = (.ok (checked.artifact,checked.order),b)
  request : ∃ a b, (readRequest checked.requestBytes).run a = (.ok checked.request,b)
  core : ∃ a, (Qirf.ContextSector.check checked.artifact checked.order checked.request.source.moduleName
    checked.request.source.functionName checked.request.positions checked.request.sites).run a = (.ok checked.result,left)

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
