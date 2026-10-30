import Protocol.OrdinaryRoot
import QleisliKernel.Qirf.RuntimeFamily

/-! Internal mixed runtime-root transport. No source syntax or external schema
is admitted here. The original graph, full types and actual storage are read
afresh and passed to the common complete-input/history gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.RuntimeRoot
open Lean Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

private def number (value : Json) : Except String Nat := do
  let n ← value.getNat?
  if n > 4294967295 then throw "runtime index exceeds u32"
  return n

private def basis (value : Json) : Except String Semantics.FiniteCarrier.Basis := do
  let atoms ← value.getArr?
  if atoms.size > 128 then throw "runtime finite basis capacity"
  atoms.toList.mapM Carrier.atom

private def typeAtom (value : Json) : Except String Semantics.RuntimeType.Atom := do
  match ← (← value.getObjVal? "tag").getStr? with
  | "quantum" => Carrier.fields value ["tag"]; return .quantum
  | "finite" =>
    Carrier.fields value ["tag","atom"]
    return .finite (← Carrier.atom (← value.getObjVal? "atom"))
  | _ => throw "unknown runtime type atom"

private def typeTree (value : Json) : Except String Semantics.RuntimeType.Tree := do
  let atoms ← value.getArr?
  if atoms.size > 384 then throw "runtime type capacity"
  atoms.toList.mapM typeAtom

private def storageAtom (value : Json) : Except String Semantics.RuntimeStorage.Atom := do
  let get := value.getObjVal?
  match ← (← get "tag").getStr? with
  | "ordinary" =>
    Carrier.fields value ["tag","basis","storage"]
    return .ordinary (← basis (← get "basis")) (← OrdinaryRoot.readStorage (← get "storage"))
  | "quantum" =>
    Carrier.fields value ["tag","owner"]
    return .quantum (← Carrier.readOwner (← get "owner"))
  | "tuple" => Carrier.fields value ["tag","arity"]; return .tuple (← number (← get "arity"))
  | _ => throw "unknown runtime storage atom"

private def storage (value : Json) : Except String Semantics.RuntimeStorage.Value := do
  let atoms ← value.getArr?
  if atoms.size > 384 then throw "runtime storage capacity"
  atoms.toList.mapM storageAtom

def decode (value : Json) : WorkM Qirf.RuntimeFamily.Request := do
  adapt (Carrier.fields value
    ["format","version","profile","selection","module","declaration","parameters","input_storage",
      "input_rows","result","storage","public_effect"])
  let get := value.getObjVal?
  guard (← adapt (do return (← (← get "format").getStr?) == "qleisli.runtime-root-request" &&
    (← number (← get "version")) == 1 &&
    (← (← get "profile").getStr?) == "finite-runtime-root-v1")) .request
  let selection ← adapt (do match ← (← get "selection").getStr? with
    | "project" => pure SourceTypes.OrdinarySignature.Selection.project
    | "exported" => pure .exported
    | "internal" => pure .internal
    | _ => throw "unknown runtime entry selection")
  let owner ← adapt ((← adapt (get "module")).getStr?)
  let name ← adapt ((← adapt (get "declaration")).getStr?)
  let parameters ← adapt ((← adapt (get "parameters")).getArr?)
  guard (parameters.size ≤ 64) .limit
  let parameters ← adapt (parameters.toList.mapM typeTree)
  guard ((parameters.map List.length).sum ≤ 384) .limit
  let inputs ← adapt ((← adapt (get "input_storage")).getArr?)
  guard (inputs.size ≤ 64) .limit
  let inputs ← adapt (inputs.toList.mapM storage)
  guard ((inputs.map List.length).sum ≤ 384) .limit
  OrdinaryRoot.checkStorageBudget ((inputs.flatMap Semantics.RuntimeStorage.ordinary).map (·.2))
  let rows ← adapt ((← adapt (get "input_rows")).getArr?)
  guard (rows.size ≤ 64) .limit
  let rows ← adapt (rows.toList.mapM fun row => do
    let values ← row.getArr?
    if values.size > 6 then throw "runtime input row width"
    values.toList.mapM Json.getBool?)
  let result ← adapt (typeTree (← adapt (get "result")))
  let stored ← adapt (storage (← adapt (get "storage")))
  OrdinaryRoot.checkStorageBudget ((Semantics.RuntimeStorage.ordinary stored).map (·.2))
  let effect ← adapt (do match ← (← get "public_effect").getStr? with
    | "unitary" => pure Semantics.Raw.Effect.unitary
    | "isometry" => pure .iso
    | "observe" => pure .observe
    | _ => throw "unknown runtime public effect")
  return ⟨selection,owner,name,parameters,inputs,rows,result,stored,effect⟩

def readRequest (bytes : ByteArray) : WorkM Qirf.RuntimeFamily.Request := do
  let value ← adapt (do
    let some text := String.fromUTF8? bytes | throw "invalid runtime request UTF-8"
    FiniteCodec.parseWithDepth text 128)
  decode value

structure Checked where
  body : ByteArray
  requestBytes : ByteArray
  artifact : Qirf.Artifact
  order : Array Nat
  request : Qirf.RuntimeFamily.Request
  result : Qirf.RuntimeFamily.Checked artifact order request

def check (bytes : ByteArray) : WorkM Checked := do
  let (body,requestBytes) ← adapt (Validity.packet bytes)
  let some requestBytes := requestBytes | throw .request
  let (artifact,order) ← Protocol.Qirf.read body
  let request ← readRequest requestBytes
  let result ← Qirf.RuntimeFamily.check artifact order request
  return ⟨body,requestBytes,artifact,order,request,result⟩

structure Binding (bytes : ByteArray) (checked : Checked) : Prop where
  packet : Validity.packet bytes = .ok (checked.body,some checked.requestBytes)
  artifact : ∃ a b, (Protocol.Qirf.read checked.body).run a = (.ok (checked.artifact,checked.order),b)
  request : ∃ a b, (readRequest checked.requestBytes).run a = (.ok checked.request,b)
  core : ∃ a b, (Qirf.RuntimeFamily.check checked.artifact checked.order checked.request).run a =
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

end QleisliKernel.Protocol.RuntimeRoot
