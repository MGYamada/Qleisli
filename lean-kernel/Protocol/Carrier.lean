import Protocol.Validity
import QleisliKernel.Qirf.Carrier
import QleisliKernel.SourceTypes

/-! Strict internal finite-carrier request. The original artifact, nominal
declarations and exact logical map are decoded afresh. No source-body theorem,
inverse/control access or external schema is supplied by this pure profile.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.Carrier
open Lean Finite Semantics.FiniteCarrier Semantics.CarrierInterface Semantics.Exact

private def adapt {α : Type} (result : Except String α) : WorkM α :=
  lift (result.mapError fun _ => .invalid)

def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected carrier fields"

private def field (value : Json) (key : String) := value.getObjVal? key
private def text (value : Json) := value.getStr?
private def number (value : Json) : Except String Nat := do
  let n ← value.getNat?
  if n > 4294967295 then throw "carrier index exceeds u32"
  return n

def origin (value : Json) : Except String Origin := do
  fields value ["module","declaration","source"]
  return ⟨← text (← field value "module"),← text (← field value "declaration"),
    ← text (← field value "source")⟩

def atom (value : Json) : Except String Atom := do
  match ← text (← field value "tag") with
  | "unit" => fields value ["tag"]; return .unit
  | "bit" => fields value ["tag"]; return .bit
  | "bits" => fields value ["tag","width"]; return .bits (← number (← field value "width"))
  | "pair" => fields value ["tag"]; return .pair
  | "tuple" => fields value ["tag","arity"]; return .tuple (← number (← field value "arity"))
  | tag =>
    if tag != "enum" && tag != "record" then throw "unknown carrier atom"
    fields value ["tag","origin","members"]
    let source ← origin (← field value "origin")
    let names ← (← (← field value "members").getArr?).toList.mapM text
    return if tag == "enum" then .enumeration source names else .record source names

private def owner (value : Json) : Except String Owner := do
  fields value ["port","basis"]
  let port ← field value "port"
  fields port ["token","wires","bits"]
  let atoms ← (← field value "basis").getArr?
  if atoms.size > 128 then throw "carrier node capacity"
  let wires ← (← (← field port "wires").getArr?).toList.mapM number
  let bits ← number (← field port "bits")
  if bits > 255 then throw "carrier port width exceeds u8"
  return ⟨⟨← number (← field port "token"),wires,bits⟩,
    ← atoms.toList.mapM atom⟩

/-- Shared typed owner syntax. This decoder confers no acceptance. -/
def readOwner (value : Json) : Except String Owner := owner value

private def interface (value : Json) : Except String Interface := do
  fields value ["inputs","outputs","public_effect"]
  let inputs ← (← field value "inputs").getArr?
  let outputs ← (← field value "outputs").getArr?
  if inputs.size > 128 || outputs.size > 128 then throw "carrier owner capacity"
  let effect ← match ← text (← field value "public_effect") with
    | "unitary" => pure Semantics.Raw.Effect.unitary
    | "isometry" => pure .iso
    | "observe" => pure .observe
    | _ => throw "unknown public carrier effect"
  return ⟨← inputs.toList.mapM owner,← outputs.toList.mapM owner,effect⟩

/-- Shared exact typed-interface syntax; individual profiles retain their own
semantic obligations. Parsing alone issues no accepted handle. -/
def readInterface (value : Json) : Except String Interface := interface value

structure Request where
  attached : Interface
  required : Interface
  logical : Matrix

def decode (value : Json) : WorkM Request := do
  adapt (fields value ["format","version","profile","attached","required","logical"])
  let profile ← adapt (do
    return (← text (← field value "format")) == "qleisli.carrier-request" &&
      (← number (← field value "version")) == 1 &&
      (← text (← field value "profile")) == "finite-carrier-pure-v1")
  guard profile .request
  let attached ← adapt (interface (← adapt (field value "attached")))
  let required ← adapt (interface (← adapt (field value "required")))
  let logical ← FiniteCodec.readMatrixValue (← adapt (field value "logical"))
  return ⟨attached,required,logical⟩

def readRequest (bytes : ByteArray) : WorkM Request := do
  let value ← adapt (do
    let some text := String.fromUTF8? bytes | throw "invalid carrier request UTF-8"
    FiniteCodec.parseWithDepth text 128)
  decode value

def checkSources (sources : SourceTypes.Sources) (request : Request) : WorkM Unit :=
  SourceTypes.checkMany sources
    ([request.attached.inputs,request.attached.outputs,request.required.inputs,request.required.outputs].flatMap
      fun owners => owners.map (·.basis))

structure Checked where
  body : ByteArray
  requestBytes : ByteArray
  artifact : Qirf.Artifact
  order : Array Nat
  request : Request
  result : Qirf.Carrier.Checked

def check (bytes : ByteArray) : WorkM Checked := do
  let (body,requestBytes) ← adapt (Validity.packet bytes)
  let some requestBytes := requestBytes | throw .request
  let (artifact,order) ← Protocol.Qirf.read body
  let request ← readRequest requestBytes
  checkSources artifact.sources request
  let result ← Qirf.Carrier.check artifact order request.attached request.required request.logical
  return ⟨body,requestBytes,artifact,order,request,result⟩

structure Binding (bytes : ByteArray) (checked : Checked) (work left : Nat) : Prop where
  packet : Validity.packet bytes = .ok (checked.body,some checked.requestBytes)
  artifact : ∃ a b, (Protocol.Qirf.read checked.body).run a = (.ok (checked.artifact,checked.order),b)
  request : ∃ a b, (readRequest checked.requestBytes).run a = (.ok checked.request,b)
  sources : ∃ a b, (checkSources checked.artifact.sources checked.request).run a = (.ok (),b)
  core : ∃ a, (Qirf.Carrier.check checked.artifact checked.order checked.request.attached
    checked.request.required checked.request.logical).run a = (.ok checked.result,left)

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
    obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨result,e,hc,h⟩ := bind_success _ _ _ _ _ h
    have final := (pure_success _ _ _ _ h)
    rcases final with ⟨rfl,rfl⟩
    have parsed := (lift_success _ _ _ _ hp).1
    have packetBound : Validity.packet bytes = .ok packet := by
      cases value : Validity.packet bytes <;> simp_all [Except.mapError]
    refine ⟨?_,⟨a,b,ha⟩,⟨b,c,hr⟩,⟨c,d,hs⟩,⟨d,hc⟩⟩
    exact packetBound.trans (congrArg Except.ok (Prod.ext rfl requested))

end QleisliKernel.Protocol.Carrier
