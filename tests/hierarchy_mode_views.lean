import Lean
import Protocol.ExecutionView.CheckedHierarchy

/-! Compare real retained Rust plans in all five hierarchy modes. This is
bounded cross-implementation evidence; the QLV2 CLI is exercised separately.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
open Lean QleisliKernel.Protocol.ExecutionView
open CheckedHierarchy.Modes

private def mode : String → Except String Mode
  | "inspect" => .ok .inspect
  | "request" => .ok .request
  | "fourier" => .ok .fourier
  | "instrument" => .ok .instrument
  | "qpeInstrument" => .ok .qpeInstrument
  | _ => .error "unknown hierarchy mode"

private def mutations (fuel : Nat) : Value → List Value :=
  Nat.rec (fun _ => []) (fun _ recurse input =>
    let different := match input with
      | .null => Value.boolean false
      | .boolean b => .boolean (!b)
      | .natural n => .natural (n+1)
      | .text s => .text (s++"!")
      | .array _ => .null
    different :: match input with
      | .array xs => xs.zipIdx.flatMap (fun (x,i) =>
          (recurse x).map (fun changed => .array (xs.set i changed)))
      | _ => []) fuel

private def positive (selected : Mode) (bytes supplied : ByteArray) : IO Nat := do
  let checked ← match (checkMode selected bytes supplied).run 10000000 with
    | (.ok result,_) => pure result
    | (.error error,_) => throw (IO.userError ("retained Rust plan refused: " ++ reprStr error))
  let description ← match (checked.core.plan checked.matrices).run 10000000 with
    | (.ok result,_) => pure result
    | (.error error,_) => throw (IO.userError ("plan derivation failed: " ++ reprStr error))
  unless (← IO.ofExcept (encode description)) == supplied do
    throw (IO.userError "accepted comparison did not retain its original plan")
  let candidates := mutations 129 description
  for candidate in candidates do
    let changed ← IO.ofExcept (encode candidate)
    match (checkMode selected bytes changed).run 10000000 with
    | (.error .decodedView,_) => pure ()
    | _ => throw (IO.userError "divergent plan did not fail at decodedView")
  -- A bad candidate does not make the independent original inspection invalid.
  unless ((inspectMode selected bytes).run 10000000).1.isOk do
    throw (IO.userError "original inspection failed after divergent candidates")
  match (checkMode selected bytes "QDV1".toUTF8).run 10000000 with
  | (.error .invalidView,_) => pure ()
  | _ => throw (IO.userError "malformed candidate not refused")
  match (checkMode selected bytes supplied).run 0 with
  | (.error (.native .limit),_) | (.error (.native (.arithmetic .workLimit)),_) => pure ()
  | _ => throw (IO.userError "exact work exhaustion not refused")
  return candidates.length

def main (args : List String) : IO Unit := do
  let [inputs,directory] := args | throw (IO.userError "expected input fixture and capture directory")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile inputs))
  let rows ← IO.ofExcept (document.getObjValAs? (Array Json) "rows")
  let mut positives := 0
  let mut negatives := 0
  let mut refusals := 0
  for index in [:rows.size] do
    let row := rows[index]!
    let selected ← IO.ofExcept (row.getObjValAs? String "mode" >>= mode)
    let name ← IO.ofExcept (row.getObjValAs? String "name")
    let bytes ← IO.FS.readBinFile (directory ++ "/" ++ toString index ++ ".bridge")
    if ← IO.ofExcept (row.getObjValAs? Bool "accept") then
      let supplied ← IO.FS.readBinFile (directory ++ "/" ++ toString index ++ ".qdv")
      let count ← positive selected bytes supplied
      positives := positives+1
      refusals := refusals+count
      IO.println (name ++ ": retained plan compared; " ++ toString count ++ " mutations refused")
    else
      -- Correct framing or a caller-provided plan cannot hide failed original
      -- independent finite-pair or exact phase-fixed H obligations.
      let supplied ← IO.FS.readBinFile (directory ++ "/0.qdv")
      for result in [((inspectMode selected bytes).run 10000000).1,
          ((checkMode selected bytes supplied).run 10000000).1] do
        match result with
        | .error (.native .equation) => pure ()
        | .error error => throw (IO.userError (name ++ ": wrong refusal " ++ reprStr error))
        | .ok _ => throw (IO.userError (name ++ ": invalid original accepted"))
      negatives := negatives+1
  unless positives == 5 && negatives == 3 do throw (IO.userError "missing native mode controls")
  IO.println ("hierarchy mode comparisons: 5 modes; 3 invalid originals; " ++
    toString refusals ++ " divergent plans refused; pure-gate evidence; QLV2 CLI exercised separately")
