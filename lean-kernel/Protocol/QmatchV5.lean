import Protocol.Carrier
import Protocol.RuntimeRoot
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.SourceTypes.StaticTypes
import QleisliKernel.Qirf.RuntimeContextRequest

/-! Strict v5 data preparation, paired with the retained Rust request.
This module issues no handle and has no production dispatcher. The complete
original operation/body obligations must precede any execution-view admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.QmatchV5
open Lean Finite Semantics.CarrierInterface SourceTypes

def profile := "finite-source-qmatch-context-v5"

private def adapt {α : Type} (value : Except String α) : WorkM α := lift (value.mapError fun _ => .invalid)
private def field (value : Json) (key : String) := value.getObjVal? key
private def number (value : Json) : Except String Nat := do
  let value ← value.getNat?
  if value > 4294967295 then throw "qmatch index exceeds u32"
  return value
private def text (value : Json) : Except String String := do
  let value ← value.getStr?
  if value.isEmpty || value.utf8ByteSize > 4096 then throw "qmatch name capacity"
  return value
private def basis (value : Json) : Except String Semantics.FiniteCarrier.Basis := do
  let atoms ← value.getArr?
  if atoms.size > 128 then throw "qmatch static basis capacity"
  atoms.toList.mapM Carrier.atom

private def bases (value : Json) : Except String (List (String × Semantics.FiniteCarrier.Basis)) := do
  (← value.getArr?).toList.mapM fun value => do
    Carrier.fields value ["name","basis"]
    return (← text (← field value "name"),← basis (← field value "basis"))
private def naturals (value : Json) : Except String (List (String × Nat)) := do
  (← value.getArr?).toList.mapM fun value => do
    Carrier.fields value ["name","value"]
    return (← text (← field value "name"),← number (← field value "value"))
private def references (value : Json) : Except String (List (String × Nat)) := do
  (← value.getArr?).toList.mapM fun value => do
    Carrier.fields value ["name","node"]
    return (← text (← field value "name"),← number (← field value "node"))

private def node (value : Json) : Except String OperationDescription.Node := do
  let get := field value
  match ← (← get "tag").getStr? with
  | "provider" | "formal" =>
    let formal := (← (← get "tag").getStr?) == "formal"
    Carrier.fields value (if formal then
      ["tag","module","function","static_bases","static_naturals","static_operations","ordinal"] else
      ["tag","module","function","static_bases","static_naturals","static_operations"])
    let b ← get "static_bases"; let n ← get "static_naturals"; let o ← get "static_operations"
    if (← b.getArr?).size+(← n.getArr?).size+(← o.getArr?).size > 32 then throw "qmatch static argument capacity"
    let owner ← text (← get "module"); let name ← text (← get "function")
    let b ← bases b; let n ← naturals n; let o ← references o
    if formal then return .formal owner name b n o (← number (← get "ordinal"))
    else return .provider owner name b n o
  | "primitive" =>
    Carrier.fields value ["tag","kind","target"]
    let kind ← match ← (← get "kind").getStr? with
      | "h" => pure OperationDescription.Primitive.h
      | "global_phase_eighth" => pure .globalPhaseEighth
      | _ => throw "unknown qmatch primitive"
    return .primitive kind (← basis (← get "target"))
  | "requested" =>
    Carrier.fields value ["tag","child","module","function"]
    return .requested (← number (← get "child")) (← text (← get "module")) (← text (← get "function"))
  | "inverse" => Carrier.fields value ["tag","child"]; return .inverse (← number (← get "child"))
  | "controlled" => Carrier.fields value ["tag","child"]; return .controlled (← number (← get "child"))
  | "then" => Carrier.fields value ["tag","left","right"]; return .thenOp (← number (← get "left")) (← number (← get "right"))
  | "tensor" => Carrier.fields value ["tag","left","right"]; return .tensor (← number (← get "left")) (← number (← get "right"))
  | "power" => Carrier.fields value ["tag","child","count"]; return .power (← number (← get "child")) (← number (← get "count"))
  | "conjugate" => Carrier.fields value ["tag","outer","middle"]; return .conjugate (← number (← get "outer")) (← number (← get "middle"))
  | _ => throw "unknown qmatch operation node"

private def description (value : Json) : Except String OperationDescription.Description := do
  Carrier.fields value ["nodes","root"]
  let nodes ← (← field value "nodes").getArr?
  if nodes.isEmpty || nodes.size > 4096 then throw "qmatch operation description capacity"
  return ⟨← nodes.toList.mapM node,← number (← field value "root")⟩

structure Source where
  moduleName : String
  functionName : String
  arguments : StaticTypes.Arguments
  deriving BEq, DecidableEq

private def source (value : Json) : Except String Source := do
  Carrier.fields value ["module","function","static_bases","static_naturals","static_operations"]
  let b ← field value "static_bases"; let n ← field value "static_naturals"; let o ← (← field value "static_operations").getArr?
  if (← b.getArr?).size+(← n.getArr?).size+o.size > 32 then throw "qmatch static argument capacity"
  let operations ← o.toList.mapM fun value => do
    Carrier.fields value ["name","description"]
    return (← text (← field value "name"),← description (← field value "description"))
  return ⟨← text (← field value "module"),← text (← field value "function"),
    ⟨← bases b,← naturals n,operations⟩⟩

abbrev Provider := Qirf.RuntimeContextRequest.Provider
abbrev Arm := Qirf.RuntimeContextRequest.Arm
abbrev Site := Qirf.RuntimeContextRequest.Site
abbrev Context := Qirf.RuntimeContextRequest.Context

-- Keep recursive transport data plain: the paired walker uses total fuel and
-- exact byte comparison, without generated partial equality/printing helpers.
structure Request where
  source : Source
  runtime : Qirf.RuntimeFamily.Request
  context : Context

/-- The runtime JSON remains the strict existing v2 object. Its operation
actuals come exclusively from this same original qmatch source instance. -/
def Request.combinedRuntime (request : Request) : Qirf.RuntimeFamily.Request :=
  {request.runtime with staticArguments := request.source.arguments}

def Request.compatible (request : Request) : Bool :=
  request.source.moduleName == request.runtime.moduleName &&
  request.source.functionName == request.runtime.declarationName &&
  request.source.arguments.bases == request.runtime.staticArguments.bases &&
  request.source.arguments.naturals == request.runtime.staticArguments.naturals

private def position (value : Json) : Except String Qirf.SourceSequence.Position := do
  Carrier.fields value ["offset","start","count"]
  return ⟨← number (← field value "offset"),← number (← field value "start"),← number (← field value "count")⟩
private def provider (value : Json) : Except String Provider := do
  match ← (← field value "kind").getStr? with
  | "function" => Carrier.fields value ["kind","evidence"]; return .function (← number (← field value "evidence"))
  | "pure" => Carrier.fields value ["kind","program"]; return .pure (← number (← field value "program"))
  | _ => throw "unknown qmatch provider subject"
private def arm (value : Json) : Except String Arm := do
  Carrier.fields value ["implementation","controlled"]
  return ⟨← number (← field value "implementation"),← number (← field value "controlled")⟩
private def site (value : Json) : WorkM Site := do
  adapt (Carrier.fields value ["attached","required","position","arms"])
  let attached ← adapt (Carrier.readInterface (← adapt (field value "attached")))
  let required ← adapt (Carrier.readInterface (← adapt (field value "required")))
  let position ← adapt (position (← adapt (field value "position")))
  let arms ← adapt ((← adapt (field value "arms")).getArr?)
  guard (0 < arms.size && arms.size ≤ 64) .limit
  return ⟨attached,required,position,← adapt (arms.toList.mapM arm)⟩

private def context : Nat → Json → WorkM Context
  | 0,_ => throw .limit
  | fuel+1,value => do
    let positions ← adapt ((← adapt (field value "positions")).getArr?)
    let sites ← adapt ((← adapt (field value "sites")).getArr?)
    let calls ← adapt ((← adapt (field value "calls")).getArr?)
    let branches ← adapt ((← adapt (field value "branches")).getArr?)
    let bodies ← adapt ((← adapt (field value "bodies")).getArr?)
    guard (sites.size ≤ 128) .limit
    exactWork (Exact.charge (16*(positions.size+sites.size+calls.size+branches.size+bodies.size+1)))
    let positions ← adapt (positions.toList.mapM position)
    let sites ← sites.toList.mapM site
    let calls ← calls.toList.mapM fun value => do
      adapt (Carrier.fields value ["position","body"])
      let position ← adapt (position (← adapt (field value "position")))
      let body ← adapt (field value "body")
      adapt (Carrier.fields body ["positions","sites","calls","branches","bodies"])
      return (position,← context fuel body)
    let branches ← branches.toList.mapM fun value => do
      adapt (Carrier.fields value ["position","then","else"])
      let location ← adapt (position (← adapt (field value "position")))
      let whenTrue ← adapt (field value "then")
      let whenFalse ← adapt (field value "else")
      adapt (Carrier.fields whenTrue ["positions","sites","calls","branches","bodies"])
      adapt (Carrier.fields whenFalse ["positions","sites","calls","branches","bodies"])
      return (location,← context fuel whenTrue,← context fuel whenFalse)
    let bodies ← bodies.toList.mapM fun value => do
      adapt (Carrier.fields value ["subject","body"])
      let subject ← adapt (provider (← adapt (field value "subject")))
      let body ← adapt (field value "body")
      adapt (Carrier.fields body ["positions","sites","calls","branches","bodies"])
      return (subject,← context fuel body)
    return .mk positions sites calls branches bodies

def decode (value : Json) : WorkM Request := do
  adapt (Carrier.fields value ["format","version","profile","source","runtime","positions","sites","calls","branches","bodies"])
  guard (← adapt (do return (← (← field value "format").getStr?) == "qleisli.qmatch-request" &&
    (← number (← field value "version")) == 5 && (← (← field value "profile").getStr?) == profile)) .request
  let source ← adapt (source (← adapt (field value "source")))
  let runtime ← Protocol.RuntimeRoot.decode (← adapt (field value "runtime"))
  let names := source.moduleName.utf8ByteSize+source.functionName.utf8ByteSize+
    runtime.moduleName.utf8ByteSize+runtime.declarationName.utf8ByteSize+
    ((source.arguments.bases ++ runtime.staticArguments.bases).map fun (name,_) => name.utf8ByteSize).sum+
    ((source.arguments.naturals ++ runtime.staticArguments.naturals).map fun (name,_) => name.utf8ByteSize).sum
  exactWork (Exact.charge (16*(names+Raw.OwnerFlow.fields
    ((source.arguments.bases ++ runtime.staticArguments.bases).map fun (_,basis) => ⟨0,basis⟩)+1)))
  let body ← context 129 value
  let request : Request := ⟨source,runtime,body⟩
  guard request.compatible .request
  return request

def readRequest (bytes : ByteArray) : WorkM Request := do
  let value ← adapt (do
    let some text := String.fromUTF8? bytes | throw "invalid qmatch request UTF-8"
    FiniteCodec.parseWithDepth text 128)
  decode value

end QleisliKernel.Protocol.QmatchV5
