import Protocol.Carrier
import QleisliKernel.Qirf.OrdinaryFamily

/-! Internal ordinary-input/result request. Decode original types and complete
storage forests afresh, then reuse the original Raw/root and every-input/history checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.OrdinaryRoot
open Lean Finite Semantics.FiniteCarrier Semantics.OrdinaryValue

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

private def number (value : Json) : Except String Nat := do
  let n ← value.getNat?
  if n > 4294967295 then throw "ordinary index exceeds u32"
  return n

private def ids (value : Json) : Except String (List Nat) := do
  let values ← value.getArr?
  if values.size > 6 then throw "ordinary storage width"
  values.toList.mapM number

private def storage : Nat → Json → Except String Storage :=
  Nat.rec (fun _ => throw "ordinary storage depth") (fun _ next value => do
    let get := value.getObjVal?
    match ← (← get "tag").getStr? with
    | "unit" => Carrier.fields value ["tag"]; return .unit
    | "bit" => Carrier.fields value ["tag","id"]; return .bit (← number (← get "id"))
    | "bits" => Carrier.fields value ["tag","ids"]; return .bits (← ids (← get "ids"))
    | "enum" =>
      Carrier.fields value ["tag","origin","ids"]
      return .enumeration (← Carrier.origin (← get "origin")) (← ids (← get "ids"))
    | "pair" =>
      Carrier.fields value ["tag","first","second"]
      return .pair (← next (← get "first")) (← next (← get "second"))
    | "tuple" =>
      Carrier.fields value ["tag","fields"]
      let fields ← (← get "fields").getArr?
      if fields.size > 128 then throw "ordinary storage arity"
      return .tuple (← fields.toList.mapM next)
    | "record" =>
      Carrier.fields value ["tag","origin","fields"]
      let source ← Carrier.origin (← get "origin")
      let fields ← (← get "fields").getArr?
      if fields.size > 128 then throw "ordinary storage arity"
      let fields ← fields.toList.mapM fun field => do
        Carrier.fields field ["name","value"]
        return (← (← field.getObjVal? "name").getStr?,← next (← field.getObjVal? "value"))
      return .record source fields
    | _ => throw "unknown ordinary storage tag")

private def storageBudget : Nat → List (Storage × Nat) → Nat → Nat → WorkM Unit :=
  Nat.rec (fun _ _ _ => throw .limit) (fun _ next pending nodes bits => do
    match pending with
    | [] => pure ()
    | (stored,depth) :: rest =>
      exactWork (Exact.charge 1)
      guard (nodes < 128 && depth ≤ 32 && pending.length ≤ 128 && bits ≤ 6) .limit
      let (children,width) : List Storage × Nat := match stored with
        | .unit => ([],0)
        | .bit _ => ([],1)
        | .bits ids | .enumeration _ ids => ([],ids.length)
        | .pair a b => ([a,b],0)
        | .tuple fields => (fields,0)
        | .record _ fields => (fields.map (·.2),0)
      guard (bits+width ≤ 6 && children.length+rest.length ≤ 128) .limit
      next ((children.map (fun child => (child,depth+1))) ++ rest) (nodes+1) (bits+width))

/-- Reuse the same bounded ordinary storage syntax in mixed runtime forests. -/
def readStorage (value : Json) : Except String Storage := storage 33 value

def checkStorageBudget (values : List Storage) : WorkM Unit :=
  storageBudget 129 (values.map (fun value => (value,0))) 0 0

def decode (value : Json) : WorkM Qirf.OrdinaryFamily.Request := do
  adapt (Carrier.fields value
    ["format","version","profile","selection","module","declaration","parameters","input_storage",
      "input_rows","basis","storage","public_effect"])
  let get := value.getObjVal?
  guard (← adapt (do return (← (← get "format").getStr?) == "qleisli.ordinary-root-request" &&
    (← number (← get "version")) == 2 &&
    (← (← get "profile").getStr?) == "finite-ordinary-root-v2") ) .request
  let selection ← adapt (do match ← (← get "selection").getStr? with
    | "project" => pure SourceTypes.OrdinarySignature.Selection.project
    | "exported" => pure .exported
    | "internal" => pure .internal
    | _ => throw "unknown ordinary entry selection")
  let owner ← adapt ((← adapt (get "module")).getStr?)
  let name ← adapt ((← adapt (get "declaration")).getStr?)
  let parameters ← adapt ((← adapt (get "parameters")).getArr?)
  guard (parameters.size ≤ 64) .limit
  let parameters ← adapt (parameters.toList.mapM fun parameter => do
    let atoms ← parameter.getArr?
    if atoms.size > 128 then throw "ordinary parameter basis capacity"
    atoms.toList.mapM Carrier.atom)
  guard ((parameters.map List.length).sum ≤ 128) .limit
  let inputs ← adapt ((← adapt (get "input_storage")).getArr?)
  guard (inputs.size ≤ 64) .limit
  let inputs ← adapt (inputs.toList.mapM (storage 33))
  storageBudget 129 (inputs.map (fun value => (value,0))) 0 0
  let rows ← adapt ((← adapt (get "input_rows")).getArr?)
  guard (rows.size ≤ 64) .limit
  let rows ← adapt (rows.toList.mapM fun row => do
    let values ← row.getArr?
    if values.size > 6 then throw "ordinary input row width"
    values.toList.mapM Json.getBool?)
  let atoms ← adapt ((← adapt (get "basis")).getArr?)
  guard (atoms.size ≤ 128) .limit
  let basis ← adapt (atoms.toList.mapM Carrier.atom)
  let stored ← adapt (storage 33 (← adapt (get "storage")))
  storageBudget 129 [(stored,0)] 0 0
  let effect ← adapt (do match ← (← get "public_effect").getStr? with
    | "unitary" => pure Semantics.Raw.Effect.unitary
    | "isometry" => pure .iso
    | "observe" => pure .observe
    | _ => throw "unknown ordinary public effect")
  return ⟨selection,owner,name,parameters,inputs,rows,basis,stored,effect⟩

def readRequest (bytes : ByteArray) : WorkM Qirf.OrdinaryFamily.Request := do
  let value ← adapt (do
    let some text := String.fromUTF8? bytes | throw "invalid ordinary request UTF-8"
    FiniteCodec.parseWithDepth text 128)
  decode value

structure Checked where
  body : ByteArray
  requestBytes : ByteArray
  artifact : Qirf.Artifact
  order : Array Nat
  request : Qirf.OrdinaryFamily.Request
  result : Qirf.OrdinaryFamily.Checked artifact order request

def check (bytes : ByteArray) : WorkM Checked := do
  let (body,requestBytes) ← adapt (Validity.packet bytes)
  let some requestBytes := requestBytes | throw .request
  let (artifact,order) ← Protocol.Qirf.read body
  let request ← readRequest requestBytes
  let result ← Qirf.OrdinaryFamily.check artifact order request
  return ⟨body,requestBytes,artifact,order,request,result⟩

structure Binding (bytes : ByteArray) (checked : Checked) : Prop where
  packet : Validity.packet bytes = .ok (checked.body,some checked.requestBytes)
  artifact : ∃ a b, (Protocol.Qirf.read checked.body).run a = (.ok (checked.artifact,checked.order),b)
  request : ∃ a b, (readRequest checked.requestBytes).run a = (.ok checked.request,b)
  core : ∃ a b, (Qirf.OrdinaryFamily.check checked.artifact checked.order checked.request).run a =
    (.ok checked.result,b)

theorem check_binding (bytes : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes).run work = (.ok checked,left)) : Binding bytes checked := by
  unfold check at ok
  obtain ⟨packet,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  cases requested : packet.2 with
  | none => simp only [requested] at h; cases h
  | some requestBytes =>
    simp only [requested] at h
    obtain ⟨decoded,b,ha,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨request,c,hr,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨result,d,hc,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
    have packetBound : Validity.packet bytes = .ok packet := by
      have parsed := (lift_success _ _ _ _ hp).1
      cases value : Validity.packet bytes <;> simp_all [Except.mapError]
    refine ⟨?_,⟨a,b,ha⟩,⟨b,c,hr⟩,⟨c,left,hc⟩⟩
    exact packetBound.trans (congrArg Except.ok (Prod.ext rfl requested))

end QleisliKernel.Protocol.OrdinaryRoot
