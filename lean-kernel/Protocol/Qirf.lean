import Protocol.Observation
import QleisliKernel.Qirf

/-! Unproved strict QIRF1/2 adapter. The native kernel checks actual table
edges and original bodies independently of the proposed scheduling order.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.Qirf
open Lean QleisliKernel.Semantics.Finite

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing QIRF fields"
private def field (value : Json) (key : String) := value.getObjVal? key
private def number (value : Json) : Except String Nat := do
  let n ← value.getNat?
  if n > 4294967295 then throw "QIRF index exceeds u32"
  return n

def basis (fuel : Nat) : Json → Except String Basis :=
  Nat.rec (fun _ => throw "type depth limit") (fun _ recurse value => do
    match ← (← field value "tag").getStr? with
    | "unit" => fields value ["tag"]; pure [.unit]
    | "bit" => fields value ["tag"]; pure [.bit]
    | "bits" =>
      fields value ["tag","width"]
      return [.bits (← number (← field value "width"))]
    | "pair" =>
      fields value ["tag","left","right"]
      return .pair :: ((← recurse (← field value "left")) ++ (← recurse (← field value "right")))
    | "tuple" =>
      fields value ["tag","fields"]
      let values ← (← field value "fields").getArr?
      if values.size < 3 then throw "noncanonical tuple arity"
      return .tuple values.size :: (← values.toList.mapM recurse).flatten
    | _ => throw "unknown legacy basis") fuel

def artifact (value : Json) : Except String QleisliKernel.Qirf.Artifact := do
  fields value ["format","version","profile","sources","programs","evidence","root","root_interface"]
  let version ← number (← field value "version")
  if (← (← field value "format").getStr?) != "qleisli.finite-ir" ||
      !((version == 1 && (← (← field value "profile").getStr?) == "finite-v0") ||
        (version == 2 && (← (← field value "profile").getStr?) == "finite-meaning-v1")) then
    throw "unknown QIRF profile"
  let sources ← (← (← field value "sources").getArr?).mapM fun source => do
    fields source ["path","text"]
    return (← (← field source "path").getStr?,← (← field source "text").getStr?)
  let programs ← (← (← field value "programs").getArr?).mapM Observation.program
  let entries ← (← (← field value "evidence").getArr?).mapM fun entry => do
    let tag ← if version == 1 then pure "circuit" else (← field entry "tag").getStr?
    fields entry ((if version == 1 then [] else ["tag"]) ++
      ["signature","implementation",if tag == "circuit" then "specification" else "meaning","identity"])
    let signature ← basis 129 (← field entry "signature")
    let target ← if tag == "circuit" then do
        pure (QleisliKernel.Qirf.Target.circuit (← number (← field entry "specification")))
      else if tag == "meaning" && version == 2 then do
        let meaning ← field entry "meaning"
        fields meaning ["tag","table"]
        let tag ← (← field meaning "tag").getStr?
        let table ← (← (← field meaning "table").getArr?).toList.mapM number
        if tag == "permutation" then
          if !table.all (· ≤ 65535) then throw "permutation table exceeds u16"
          else pure (.permutation table)
        else if tag == "phase8" then
          if !table.all (· ≤ 255) then throw "phase table exceeds u8"
          else pure (.phase8 table)
        else throw "unknown meaning target"
      else throw "unknown evidence target"
    let identity ← field entry "identity"
    fields identity ["implementation","specification","sources"]
    return ⟨signature,← number (← field entry "implementation"),target,
      ← (← field identity "implementation").getStr?,← (← field identity "specification").getStr?,
      ← (← (← field identity "sources").getArr?).toList.mapM number⟩
  let rootInterface ← match ← field value "root_interface" with
    | .null => pure none
    | interface => do
      fields interface ["input","output"]
      pure (some (← basis 129 (← field interface "input"),← basis 129 (← field interface "output")))
  return ⟨programs,entries,sources,← number (← field value "root"),rootInterface⟩

private def visit (nodes : Hierarchical.Graph.Nodes) (fuel : Nat) :
    Nat → (Array Nat × Array Nat) → Except String (Array Nat × Array Nat) :=
  Nat.rec (fun _ _ => throw "QIRF graph depth limit") (fun _ recurse index (colors,order) => do
    let some color := colors[index]? | throw "QIRF reference outside graph"
    if color == 2 then return (colors,order)
    if color == 1 then throw "QIRF dependency cycle"
    let (colors,order) ← (Hierarchical.Graph.dependencies nodes index).foldlM
      (fun state child => recurse child state) (colors.set! index 1,order)
    return (colors.set! index 2,order.push index)) fuel

def read (bytes : ByteArray) : QleisliKernel.Finite.WorkM (QleisliKernel.Qirf.Artifact × Array Nat) := do
  let parsed : Except String (QleisliKernel.Qirf.Artifact × Array Nat) := do
    let some text := String.fromUTF8? bytes | throw "invalid QIRF UTF-8"
    let artifact ← artifact (← FiniteCodec.parseWithDepth text 128)
    if artifact.programs.size + artifact.entries.size > 65536 then throw "QIRF table limit"
    let nodes := QleisliKernel.Qirf.nodes artifact
    let (_,order) ← visit nodes 33 artifact.root (Array.replicate nodes.size 0,#[])
    return (artifact,order)
  QleisliKernel.Finite.lift (parsed.mapError (fun _ => .invalid))

end QleisliKernel.Protocol.Qirf
