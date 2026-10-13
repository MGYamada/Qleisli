import Protocol.FiniteCodec

/-! Test-only entry to the actual JSON prescan, including its final Lean parser.
No QIRF acceptance or semantic guarantee follows from accepting JSON here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
def main (args : List String) : IO UInt32 := do
  let [path, depth] := args | throw (IO.userError "expected file and depth")
  let some depth := depth.toNat? | throw (IO.userError "expected depth")
  let text ← IO.FS.readFile path
  match QleisliKernel.Protocol.FiniteCodec.parseWithDepth text depth with
  | .ok _ => IO.println "accepted"; return 0
  | .error error => IO.println ("error\n" ++ error); return 1
