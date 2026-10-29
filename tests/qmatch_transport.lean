import Lean
import Protocol.ExecutionView.CheckedQmatch
import Protocol.NativeContext.Bindings

/-! Independent shared data expectations for the actual named-arm protocol.
The QLV3 comparison and context-dispatch definitions run directly; fresh native
compilation and Rust accepted-handle tests remain separate obligations. No maximal quantum
system is generated; the two accepted controls use Unit owners and one Bit for
the separately checked controlled implementation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
open Lean QleisliKernel QleisliKernel.Protocol.ExecutionView

private def value (fuel : Nat) : Json → Except String Value :=
  Nat.rec (fun _ => throw "qmatch vector depth") (fun _ recurse input => do
    match input with
    | .null => return .null
    | .bool b => return .boolean b
    | .num _ => return .natural (← input.getNat?)
    | .str s => return .text s
    | .arr xs => return .array (← xs.toList.mapM recurse)
    | .obj _ => throw "qmatch view contains an object") fuel

private def u32 (value : Nat) : ByteArray :=
  ⟨((List.range 4).map (fun index => (value / 256^index % 256).toUInt8)).toArray⟩

private def packet (body required : ByteArray) : ByteArray :=
  "QLV1".toUTF8 ++ u32 body.size ++ u32 required.size ++ body ++ required

private def envelope (original graph : ByteArray) (scope : Nat := 1) : ByteArray :=
  "QLV3".toUTF8 ++ u32 2026 ++ u32 scope ++ u32 original.size ++ u32 graph.size ++
    u32 0 ++ u32 0 ++ original ++ graph

private def cases (path : System.FilePath) : IO (Array Json) := do
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept ((parsed.getObjVal? "cases") >>= Json.getArr?)

private def shapes (path : System.FilePath) : IO Unit := do
  let rows ← cases path
  unless rows.size == 33 do throw (IO.userError "qmatch shape inventory changed")
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let text ← IO.ofExcept ((row.getObjVal? "text") >>= Json.getStr?)
    let expected ← IO.ofExcept ((row.getObjVal? "accepted") >>= Json.getBool?)
    let actual := ((Protocol.Qmatch.readRequest text.toUTF8).run 10000000).1.isOk
    unless actual == expected do throw (IO.userError ("qmatch data mismatch: " ++ name))
  IO.println "passed 33 shared Rust/Lean request shape expectations; parsing confers no acceptance"

private def execution (path : System.FilePath) : IO Unit := do
  let rows ← cases path
  unless rows.size == 26 do throw (IO.userError "qmatch execution inventory changed")
  let mut accepts := 0
  let mut refusals := 0
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let artifact ← IO.ofExcept (row.getObjVal? "artifact")
    let required ← IO.ofExcept (row.getObjVal? "request")
    let original := packet artifact.compress.toUTF8 required.compress.toUTF8
    let supplied ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    let expected ← IO.ofExcept ((row.getObjVal? "accepted") >>= Json.getBool?)
    let framed := envelope original supplied
    let actual := (CheckedQmatch.run framed).run 10000000
    let dispatched := (Protocol.NativeContext.run .qmatchSource Protocol.productVersion framed).run 10000000
    unless dispatched.1.isOk == actual.1.isOk && dispatched.2 == actual.2 do
      throw (IO.userError ("qmatch context changed the original decision/work: " ++ name))
    match (Protocol.NativeContext.run .qmatchSource "wrong-product" framed).run 10000000 with
    | (.error .version,10000000) => pure ()
    | _ => throw (IO.userError "qmatch context accepted a different product")
    match actual.1 with
    | .ok checked =>
      unless expected && checked.body == artifact.compress.toUTF8 &&
          checked.requestBytes == required.compress.toUTF8 do
        throw (IO.userError ("qmatch original bytes/acceptance mismatch: " ++ name))
      accepts := accepts+1
      let .ok decision := dispatched.1 | throw (IO.userError "qmatch context lost successful input")
      let lines := Protocol.NativeContext.successLines .qmatchSource decision (10000000-dispatched.2)
      unless lines.take 6 == ["qleisli.native-result 3","accepted","2026",Protocol.productVersion,
          "--qmatch-source-check","execution"] && lines.drop 7 == ["1"] do
        throw (IO.userError "qmatch response lost its actual context/request binding")
      match (Protocol.NativeContext.run .qmatchSource Protocol.productVersion
          (envelope original ByteArray.empty 0)).run 10000000 with
      | (.error .packet,_) => pure ()
      | _ => throw (IO.userError "qmatch context accepted inspection scope")
      let caller ← IO.ofExcept (encode (.array []))
      let callerEnvelope := "QLV3".toUTF8 ++ u32 2026 ++ u32 2 ++ u32 original.size ++
        u32 supplied.size ++ u32 caller.size ++ u32 0 ++ original ++ supplied ++ caller
      match (Protocol.NativeContext.run .qmatchSource Protocol.productVersion callerEnvelope).run 10000000 with
      | (.error .packet,_) => pure ()
      | _ => throw (IO.userError "qmatch context accepted caller scope")
      -- Valid original bytes and view grant no inspection/caller execution.
      for scope in [0,2] do
        match ((CheckedQmatch.input ⟨.e2026,if scope == 0 then .inspection else .caller,
            original,supplied,ByteArray.empty,[]⟩).run 10000000).1 with
        | .error .packet => pure ()
        | _ => throw (IO.userError "qmatch non-execution scope did not refuse at the scope gate")
      if ((CheckedQmatch.run (envelope original supplied)).run 0).1.isOk then
        throw (IO.userError "qmatch exhausted work accepted")
    | .error error =>
      if expected then throw (IO.userError ("qmatch valid original rejected: " ++ name ++ ": " ++ reprStr error))
      let kind ← IO.ofExcept ((row.getObjVal? "error") >>= Json.getStr?)
      let correct := match kind,error with
        | "decodedView",.decodedView => true
        | "native",.native _ => true
        | _,_ => false
      unless correct do throw (IO.userError ("qmatch wrong refusal stage: " ++ name ++ ": " ++ reprStr error))
      refusals := refusals+1
  unless accepts == 2 && refusals == 24 do throw (IO.userError "qmatch coverage changed")
  IO.println "passed 2 exact phase controls and 24 QLV3 source/body/evidence/view refusals, including actual context dispatch; fresh native compilation/handle tests remain separate"

def main (args : List String) : IO Unit := do
  let [shapePath,executionPath] := args | throw (IO.userError "expected qmatch shape and execution fixtures")
  shapes shapePath
  execution executionPath
