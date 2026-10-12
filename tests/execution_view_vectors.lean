import Lean
import Protocol.ExecutionView.Graph
import Protocol.Qirf

/-! Shared QDV1 encoding vectors. This runner checks transport bytes only.
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
    | .obj _ => throw "canonical vector contains an object") fuel

private def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun byte =>
    let digits := "0123456789abcdef".toList
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

private def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def coefficient (value : Json) : Except String QleisliKernel.Semantics.Exact.Coefficient := do
  let pair ← value.getArr?
  if pair.size != 2 then throw "expected a dyadic pair"
  let some numerator := (← pair[0]!.getStr?).toInt? | throw "expected a signed numerator"
  return ⟨numerator,← pair[1]!.getNat?⟩

private def matrix (value : Json) : Except String QleisliKernel.Semantics.Exact.Matrix := do
  let rows ← (← value.getObjVal? "rows").getNat?
  let cols ← (← value.getObjVal? "cols").getNat?
  let entries ← (← (← value.getObjVal? "entries").getArr?).toList.mapM fun scalar => do
    let cs ← (← scalar.getArr?).toList.mapM coefficient
    let [a,b,c,d] := cs | throw "expected four exact coefficients"
    return QleisliKernel.Semantics.Exact.Scalar.mk a b c d
  if entries.length != rows*cols then throw "matrix entry count"
  return ⟨rows,cols,entries⟩

private def finite (directory : System.FilePath) (row : Json) : IO Value := do
  match ← IO.ofExcept ((row.getObjVal? "kind") >>= Json.getStr?) with
  | "raw-source" =>
    let source ← IO.ofExcept ((row.getObjVal? "source") >>= Json.getStr?)
    let artifact ← IO.ofExcept (Json.parse (← IO.FS.readFile (directory / source)))
    let programs ← IO.ofExcept ((artifact.getObjVal? "programs") >>= Json.getArr?)
    if programs.size != 1 then throw (IO.userError "expected one retained root")
    IO.ofExcept (QleisliKernel.Protocol.Observation.program programs[0]! >>= FiniteView.program)
  | "raw" =>
    IO.ofExcept ((row.getObjVal? "program") >>= QleisliKernel.Protocol.Observation.program >>= FiniteView.program)
  | "basis" =>
    return FiniteView.basis (← IO.ofExcept ((row.getObjVal? "basis") >>= QleisliKernel.Protocol.Qirf.basis 129))
  | "matrix" => return FiniteView.matrix (← IO.ofExcept ((row.getObjVal? "matrix") >>= matrix))
  | _ => throw (IO.userError "unknown finite vector kind")

private def functionInput (row : Json) : Except String QleisliKernel.Semantics.ObservingFunction.Input := do
  let signature ← (← row.getObjVal? "signature") |> QleisliKernel.Protocol.Qirf.basis 129
  let implementation ← (← row.getObjVal? "implementation") |> QleisliKernel.Protocol.Observation.program
  let specification ← (← row.getObjVal? "specification") |> QleisliKernel.Protocol.Observation.program
  let identity ← row.getObjVal? "identity"
  let sources ← (← (← identity.getObjVal? "sources").getArr?).toList.mapM fun source => do
    let pair ← source.getArr?
    if pair.size != 2 then throw "expected source pair"
    return (← pair[0]!.getStr?,← pair[1]!.getStr?)
  return ⟨signature,implementation,specification,
    ⟨← (← identity.getObjVal? "implementation").getStr?,
      ← (← identity.getObjVal? "specification").getStr?,sources⟩⟩

private def checked {α : Type} (work : QleisliKernel.Finite.WorkM α) : IO α := do
  match work.run 10000000 with
  | (.ok result,_) => return result
  | (.error error,_) => throw (IO.userError ("native derivation refused: " ++ reprStr error))

def main (args : List String) : IO Unit := do
  let [path,finitePath,functionPath,graphPath] := args | throw (IO.userError "expected primitive, finite, function and graph vector files")
  let text ← IO.FS.readFile path
  let rows ← IO.ofExcept (Json.parse text >>= Json.getArr?)
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept ((row.getObjVal? "value") >>= value 129)
    let expected ← IO.ofExcept ((row.getObjVal? "hex") >>= Json.getStr?)
    let actual ← IO.ofExcept (encode input)
    unless hex actual == expected do
      throw (IO.userError ("canonical vector mismatch: " ++ name))
  unless failed (encode (.natural (2^64))) do
    throw (IO.userError "out-of-range natural accepted")
  let atDepth := (List.range maxDepth).foldl (fun v _ => Value.array [v]) Value.null
  unless (encode atDepth).isOk && failed (encode (.array [atDepth])) do
    throw (IO.userError "canonical depth limit differs")
  IO.println ("canonical encoding: " ++ toString rows.size ++ " shared vectors passed")
  let cases ← IO.ofExcept (Json.parse (← IO.FS.readFile finitePath) >>= Json.getArr?)
  let directory := (System.FilePath.mk finitePath).parent.getD "."
  for row in cases do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let actual ← IO.ofExcept (encode (← finite directory row))
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    unless actual == expected do
      throw (IO.userError ("typed finite vector mismatch: " ++ name))
  IO.println ("typed finite data: " ++ toString cases.size ++ " shared vectors passed; no acceptance claim")
  let functions ← IO.ofExcept (Json.parse (← IO.FS.readFile functionPath) >>= Json.getArr?)
  let mut before := []
  for row in functions do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept (functionInput row)
    let receipt ← checked (QleisliKernel.Raw.BranchFunction.checkEntry before input input)
    let actual ← IO.ofExcept (encode (← checked (FiniteView.functionEvidence receipt)))
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    unless actual == expected do
      throw (IO.userError ("retained function cache mismatch: " ++ name))
    before := before ++ [receipt]
  IO.println ("retained function caches: " ++ toString functions.size ++ " shared vectors passed; no production binding claim")
  let graphs ← IO.ofExcept (Json.parse (← IO.FS.readFile graphPath) >>= Json.getArr?)
  for row in graphs do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept (row.getObjVal? "artifact")
    let (artifact,order) ← checked (QleisliKernel.Protocol.Qirf.read input.compress.toUTF8)
    let retained ← checked (QleisliKernel.Qirf.Validity.checkRoot artifact order)
    let actual ← IO.ofExcept (encode (← checked (FiniteView.graph artifact retained)))
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    unless actual == expected do
      throw (IO.userError ("retained finite graph mismatch: " ++ name))
  IO.println ("retained finite graphs: " ++ toString graphs.size ++ " shared vectors passed; no production binding claim")
