import QleisliKernel.Semantics.Observation
import QleisliKernel.Semantics.Function

/-! Complete original function bodies, including closed classical branches.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.ObservingFunction
open Finite Observation

structure Input where
  signature : Basis
  implementation : Program
  specification : Program
  identity : Function.Identity

abbrev Binding := Input

structure Receipt where
  input : Input
  meaning : Exact.Matrix
  depth : Nat
  expandedSteps : Nat

def Receipt.dependency (receipt : Receipt) : Dependency :=
  ⟨receipt.input.signature,receipt.meaning⟩

/-- All original arms contribute dependency references, whether selected or not. -/
def references (fuel : Nat) : List Op → List Nat :=
  Nat.rec (fun _ => []) (fun _ recurse ops => ops.flatMap fun op => match op with
    | .pure op => (match op with
        | .applyUnitary _ _ steps => steps
        | .certifiedCompute _ _ _ _ uses logical => uses ++ logical
        | _ => []).filterMap (fun (step : Step) => match step.action with
          | .contract _ index _ => some index | _ => none)
    | .branch _ left right _ _ => recurse left ++ recurse right
    | _ => []) fuel

end QleisliKernel.Semantics.ObservingFunction
