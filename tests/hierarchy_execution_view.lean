import Lean
import Protocol.ExecutionView.CheckedHierarchy

/-! Shared hand-described hierarchy plans. Materialization controls explicitly
do not claim structural/semantic acceptance. Only the H case uses the fresh gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
open Lean QleisliKernel.Protocol.ExecutionView

private def value (fuel : Nat) : Json → Except String Value :=
  Nat.rec (fun _ => throw "vector depth") (fun _ recurse input => do
    match input with
    | .null => return .null
    | .bool b => return .boolean b
    | .num _ => return .natural (← input.getNat?)
    | .str s => return .text s
    | .arr xs => return .array (← xs.toList.mapM recurse)
    | .obj _ => throw "object in canonical vector") fuel

private def unhex (text : String) : Except String ByteArray := do
  let chars := text.toList.toArray
  if chars.size % 2 != 0 then throw "odd hex length"
  let digit := fun c => ("0123456789abcdef".toList.idxOf c)
  let mut bytes := ByteArray.empty
  for i in [:chars.size/2] do
    let a := digit chars[2*i]!
    let b := digit chars[2*i+1]!
    if a ≥ 16 || b ≥ 16 then throw "invalid hex"
    bytes := bytes.push (16*a+b).toUInt8
  return bytes

private def checked {α : Type} (action : QleisliKernel.Finite.WorkM α) : IO α := do
  match action.run 10000000 with
  | (.ok result,_) => return result
  | (.error error,_) => throw (IO.userError ("derivation refused: " ++ reprStr error))

private def mutations (fuel : Nat) : Value → List Value :=
  Nat.rec (fun _ => []) (fun _ recurse input =>
    let different := match input with
      | .null => Value.boolean false
      | .boolean b => .boolean (!b)
      | .natural n => .natural (n+1)
      | .text s => .text (s++"!")
      | .array _ => .null
    different :: match input with
      | .array xs => xs.zipIdx.flatMap (fun (x,i) => (recurse x).map (fun changed => .array (xs.set i changed)))
      | _ => []) fuel

private def gateCases (bytes : ByteArray) (description : Value) : IO Nat := do
  let supplied ← IO.ofExcept (encode description)
  match (CheckedHierarchy.checkInspect bytes supplied).run 10000000 with
  | (.ok checked,_) =>
    if checked.matrices.length != 1 then throw (IO.userError "fresh finite leaf lost")
  | (.error error,_) => throw (IO.userError ("correct hierarchy view refused: " ++ reprStr error))
  let candidates := mutations 129 description
  for candidate in candidates do
    let changed ← IO.ofExcept (encode candidate)
    match (CheckedHierarchy.checkInspect bytes changed).run 10000000 with
    | (.error .decodedView,_) => pure ()
    | other => throw (IO.userError ("divergent hierarchy description was not refused: " ++ reprStr other.1.isOk))
  match (CheckedHierarchy.checkInspect bytes "QDV1".toUTF8).run 10000000 with
  | (.error .invalidView,_) => pure ()
  | _ => throw (IO.userError "malformed hierarchy view accepted")
  match (CheckedHierarchy.checkInspect bytes supplied).run 0 with
  | (.error (.native .limit),_) => pure ()
  | (.error (.native (.arithmetic .workLimit)),_) => pure ()
  | (.error error,_) => throw (IO.userError ("wrong exhausted-work refusal: " ++ reprStr error))
  | (.ok _,_) => throw (IO.userError "exhausted exact work accepted")
  return candidates.length

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected hierarchy vector path")
  let rows ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let mut refusals := 0
  for row in rows do
    let name ← IO.ofExcept (row.getObjValAs? String "name")
    let bytes ← IO.ofExcept (row.getObjValAs? String "bridge_hex" >>= unhex)
    let scope ← IO.ofExcept (row.getObjValAs? String "scope")
    let description ← IO.ofExcept (row.getObjVal? "value" >>= value 129)
    let expected ← IO.ofExcept (encode description)
    let leaves ← IO.ofExcept (row.getObjValAs? (Array Json) "matrices")
    let matrices ← leaves.toList.mapM fun leaf => do
      let index ← IO.ofExcept (leaf.getObjValAs? Nat "definition")
      let raw ← IO.ofExcept (leaf.getObjVal? "value")
      let matrix ← checked (QleisliKernel.Protocol.HierarchicalFinite.matrix raw.compress.toUTF8)
      return (index,matrix)
    let actual ← if bytes.extract 0 4 == "QLI1".toUTF8 then do
        let parsed ← IO.ofExcept ((QleisliKernel.Protocol.Hierarchical.parseInstrument bytes).mapError reprStr)
        checked (HierarchyView.instrumentPlan parsed.packet matrices)
      else do
        let (artifact,order) ← IO.ofExcept ((QleisliKernel.Protocol.Hierarchical.parse bytes).mapError reprStr)
        if scope == "native-inspection" then
          let structural ← IO.ofExcept ((QleisliKernel.Hierarchical.Conditional.checkAll artifact order).mapError reprStr)
          let fresh ← checked (HierarchyView.reconstructLeaves structural.state.requests)
          checked (HierarchyView.purePlan artifact fresh)
        else checked (HierarchyView.purePlan artifact matrices)
    unless (← IO.ofExcept (encode actual)) == expected do
      throw (IO.userError ("hierarchy view mismatch: " ++ name))
    if scope == "native-inspection" then refusals := refusals + (← gateCases bytes description)
  IO.println ("hierarchy execution views: " ++ toString rows.size ++ " shared cases; " ++
    toString refusals ++ " divergent candidates refused; production cutover pending")
