import QleisliKernel.Semantics.Protected

/-! Original function attachments and literal expansion accounting. These are
data and independent presentations, not accepted receipts or capacity rules.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Function
open Raw Finite

structure Identity where
  implementation : String
  specification : String
  sources : List (String × String)
  deriving BEq, DecidableEq, Repr

structure Input where
  body : Raw.Evidence
  identity : Identity
  deriving BEq, DecidableEq, Repr

abbrev Binding := Input

structure Receipt where
  input : Input
  meaning : Exact.Matrix
  depth : Nat
  expandedSteps : Nat
  deriving Repr

def Receipt.dependency (receipt : Receipt) : Dependency :=
  ⟨receipt.input.body.signature,receipt.meaning⟩

def extracted : Event → Option (List Step)
  | .init0 _ => none
  | .circuit _ steps => some steps
  | .liftBasis _ _ inputAxes _ table =>
    some [⟨[],.monomial inputAxes table (List.replicate table.length 0)⟩]
  | .reorder bits axes =>
    some (if axes == List.range bits then [] else [⟨[],.monomial (List.range bits)
      ((List.range (2^bits)).map fun label => gather label axes) (List.replicate (2^bits) 0)⟩])
  | .computed _ axes _ _ _ _ steps => some (steps.map (RawTrace.localize axes))
  | .protectedComputed _ axes sourceBits _ function uses =>
    some ((uses.flatMap (Protected.logical sourceBits function)).map (RawTrace.localize axes))

def stepCost (dependencies : List Nat) (step : Step) : Option Nat :=
  match step.action with | .contract _ index _ => dependencies[index]? | _ => some 1

def countStep (dependencies : List Nat) (count : Nat) (step : Step) : Option Nat := do
  return count + (← stepCost dependencies step)

def countEvent (dependencies : List Nat) (counts : Nat × Nat) (event : Event) : Option (Nat × Nat) := do
  let steps ← extracted event
  let expanded ← steps.foldlM (countStep dependencies) counts.2
  return (counts.1 + steps.length,expanded)

def expansion (dependencies : List Nat) (events : List Event) : Option Nat := do
  let counts ← events.foldlM (countEvent dependencies) (0,0)
  return max counts.2 1

deriving instance ReflBEq, LawfulBEq for Identity, Input
end QleisliKernel.Semantics.Function
