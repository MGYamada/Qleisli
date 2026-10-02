import QleisliKernel.Semantics.Observation
import Qleisli.Semantics.Raw

/-! Independent original-operation instrument semantics. These judgments retain
every hidden outcome, classical value and unnormalized operator. They import
neither acceptance predicates nor evaluator code or work/capacity policies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawInstrument
open QleisliKernel.Semantics.Observation QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite Qleisli.Semantics.Exact

structure History where
  values : List (Nat × Bool)
  hidden : List Nat
  operator : Matrix

def value (values : List (Nat × Bool)) (id : Nat) : Option Bool :=
  (values.find? (fun pair => pair.1 == id)).map (·.2)

def expression (values : List (Nat × Bool)) : Expr → Option Bool
  | .constant v => some v
  | .not input => return !(← value values input)
  | .xor left right => return (← value values left) != (← value values right)
  | .and left right => return (← value values left) && (← value values right)

def merged (choice : Bool) (phis : List ClassicalPhi) (history : History) : Option History := do
  let values ← phis.mapM fun phi => do
    pure (phi.output,← value history.values (if choice then phi.thenId else phi.elseId))
  return {history with values := history.values ++ values}

noncomputable def ErasureMeaning (bits : Nat) (axes : List Nat) (outcome : Nat) (map : Matrix) : Prop :=
  let kept := (List.range bits).filter (fun axis => !axes.contains axis)
  map.rows = 2^kept.length ∧ map.cols = 2^bits ∧
    ∀ row col, row < map.rows → col < map.cols →
      entry map row col = if gather col axes = outcome ∧ gather col kept = row then 1 else 0

noncomputable def Erased (bits : Nat) (axes : List Nat) (output : Option Nat)
    (initial : History) (outcome : Nat) (next : History) : Prop :=
  next.hidden = initial.hidden ++ [outcome] ∧
  next.values = (match output with
    | none => initial.values
    | some id => initial.values ++ [(id,outcome == 1)]) ∧
  ∃ map, ErasureMeaning bits axes outcome map ∧
    Raw.Composition map initial.operator next.operator

mutual
  /-- Literal single-event action. Measurement/discard enumerate all basis
  outcomes; reset is erasure followed by the original fresh-zero event. -/
  inductive Action (dependencies : List Dependency) : Event → History → List History → Prop
    | pure (event) (initial : History) (next map : Matrix)
        (meaning : Raw.EventMeaning dependencies event map)
        (composition : Raw.Composition map initial.operator next) :
        Action dependencies (.pure event) initial [{initial with operator := next}]
    | erase (bits axes output initial next)
        (allOutcomes : List.Forall₂ (Erased bits axes output initial) (List.range (2^axes.length)) next) :
        Action dependencies (.erase bits axes output) initial next
    | classical (expr output initial result)
        (evaluated : expression initial.values expr = some result) :
        Action dependencies (.classical expr output) initial
          [{initial with values := initial.values ++ [(output,result)]}]
    | branch (condition thenEvents elseEvents phis initial choice middle next)
        (selected : value initial.values condition = some choice)
        (arm : Run dependencies (if choice then thenEvents else elseEvents) [initial] middle)
        (merged : List.Forall₂ (fun before after => RawInstrument.merged choice phis before = some after) middle next) :
        Action dependencies (.branch condition thenEvents elseEvents phis) initial next
  /-- Adaptive composition retains each complete intermediate family and sums
  all hidden histories by concatenation, with no normalization/postselection. -/
  inductive Run (dependencies : List Dependency) : List Event → List History → List History → Prop
    | nil (initial) : Run dependencies [] initial initial
    | cons (event events initial groups final)
        (localActions : Actions dependencies event initial groups)
        (rest : Run dependencies events groups.flatten final) :
        Run dependencies (event::events) initial final
  inductive Actions (dependencies : List Dependency) : Event → List History → List (List History) → Prop
    | nil (event) : Actions dependencies event [] []
    | cons (event initial next rest groups)
        (head : Action dependencies event initial next)
        (tail : Actions dependencies event rest groups) :
        Actions dependencies event (initial::rest) (next::groups)
end

theorem Actions.of_forall₂ (dependencies : List Dependency) (event : Event)
    (initial : List History) (groups : List (List History))
    (all : List.Forall₂ (Action dependencies event) initial groups) :
    Actions dependencies event initial groups := by
  induction all with
  | nil => exact .nil _
  | cons head tail ih => exact .cons _ _ _ _ _ head ih

noncomputable def ProgramMeaning (dependencies : List Dependency) (program : Program)
    (classical : List Bool) (histories : List History) : Prop :=
  ∃ prepared initial, QleisliKernel.Semantics.Observation.read program = some prepared ∧
    Raw.IdentityMeaning prepared.inputBits initial ∧
    Run dependencies prepared.events [⟨program.classicalInputs.zip classical,[],initial⟩] histories

end Qleisli.Semantics.RawInstrument
