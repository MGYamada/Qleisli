import Qleisli.Semantics.RawAction
import Qleisli.Semantics.RawInstrument

/-! Independent coefficient instrument semantics for arbitrary finite frames.
No global matrix, executable checker, budget or receipt is part of this model.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.ObservingAction
open QleisliKernel.Semantics.Observation QleisliKernel.Semantics.Finite

noncomputable def erase (bits : Nat) (axes : List Nat) (outcome : Nat) (ψ : Nat → ℂ) (output : Nat) : ℂ :=
  let kept := (List.range bits).filter (fun axis => !axes.contains axis)
  ((List.range (2^bits)).map fun input =>
    if gather input axes = outcome ∧ gather input kept = output then ψ input else 0).sum

structure History where
  values : List (Nat × Bool)
  hidden : List Nat
  operator : Nat → Nat → ℂ

noncomputable def initial (values : List (Nat × Bool)) : History :=
  ⟨values,[],fun row col => if row = col then 1 else 0⟩

noncomputable def merge (choice : Bool) (phis : List ClassicalPhi) (history : History) : Option History := do
  let values ← phis.mapM fun phi => do
    return (phi.output,← RawInstrument.value history.values (if choice then phi.thenId else phi.elseId))
  return {history with values := history.values ++ values}

noncomputable def step (dependencies : List Dependency)
    (recurse : List Event → History → Option (List History))
    (event : Event) (history : History) : Option (List History) :=
  match event with
  | .pure op => some [{history with operator := fun row col => RawAction.event dependencies op (fun row => history.operator row col) row}]
  | .erase bits axes output => some ((List.range (2^axes.length)).map fun outcome =>
    { values := match output with
        | none => history.values
        | some id => history.values ++ [(id,outcome == 1)]
      hidden := history.hidden ++ [outcome]
      operator := fun row col => erase bits axes outcome (fun row => history.operator row col) row })
  | .classical expr output => do
    let value ← RawInstrument.expression history.values expr
    some [{history with values := history.values ++ [(output,value)]}]
  | .branch condition left right phis => do
    let choice ← RawInstrument.value history.values condition
    let next ← recurse (if choice then left else right) history
    next.mapM (merge choice phis)

noncomputable def run (dependencies : List Dependency) (fuel : Nat) : List Event → History → Option (List History) :=
  Nat.rec (fun _ _ => none) (fun _ recurse events history =>
    events.foldlM (fun histories event => do
      let next ← histories.mapM (step dependencies recurse event)
      return next.flatten) [history]) fuel

noncomputable def program (dependencies : List Dependency) (body : Program) (classical : List Bool) : Option (List History) := do
  let prepared ← QleisliKernel.Semantics.Observation.read body
  run dependencies 65 prepared.events (initial (body.classicalInputs.zip classical))

end Qleisli.Semantics.ObservingAction
