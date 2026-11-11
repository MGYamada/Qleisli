import QleisliKernel.Qirf.RuntimeNamedThreeOccurrence

/-! Project an exact direct selection or child traversal from the retained
witness at the current source prefix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralSelectionWitness
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Node Nodes Step Steps)
open RuntimeSelectionSteps (Item Witness)

private theorem step_witness {dependencies program block step ordinal count}
    (earlier later : List (Step dependencies program block))
    (witness : @Witness dependencies (.steps ordinal (Steps.ofList (earlier ++ step :: later))) count) :
    ∃ count, Nonempty (Witness (.step (ordinal + earlier.length) step) count) := by
  induction earlier generalizing ordinal count with
  | nil =>
    change Witness (.steps ordinal (.cons step (Steps.ofList later))) count at witness
    cases witness with
    | leaf original => cases original
    | selection original _ _ => cases original
    | child original _ => cases original
    | pair original head tail =>
      cases original
      exact ⟨_,⟨head⟩⟩
  | cons first earlier ih =>
    change Witness (.steps ordinal (.cons first (Steps.ofList (earlier ++ step :: later)))) count at witness
    cases witness with
    | leaf original => cases original
    | selection original _ _ => cases original
    | child original _ => cases original
    | pair original head tail =>
      cases original
      obtain ⟨count,⟨found⟩⟩ := ih tail
      have position : ordinal+1+earlier.length = ordinal+(first::earlier).length := by
        simp only [List.length_cons]
        omega
      exact ⟨count,⟨position ▸ found⟩⟩

def Direct {dependencies program block} : Step dependencies program block → Prop
  | .pure node@(.selection ..) => Nonempty (RuntimeSelectionWitness.Checked node)
  | _ => True

/-- The direct selection witness is for the current original node, even if an
identical action occurs earlier or later in the same body. -/
theorem direct_at_step {dependencies program block steps count step}
    (witness : @Witness dependencies (.steps 0 (Steps.ofList (program := program) (block := block) steps)) count)
    (earlier later : List (Step dependencies program block))
    (split : steps = earlier ++ step :: later) : Direct step := by
  subst steps
  cases step with
  | pure node =>
    cases node
    case selection =>
      obtain ⟨_,⟨current⟩⟩ := step_witness earlier later witness
      cases current with
      | leaf original => cases original
      | selection original _ _ => cases original
      | pair original _ _ => cases original
      | child original nested =>
        cases original
        cases nested with
        | leaf original => cases original
        | child original _ => cases original
        | pair original _ _ => cases original
        | selection original literal _ =>
          cases original
          exact ⟨literal⟩
    all_goals exact True.intro
  | _ => exact True.intro

def Named {dependencies program block} : Step dependencies program block → Prop
  | .named _ _ _ _ _ _ children => ∃ count, Nonempty (Witness (.steps 0 children) count)
  | _ => True

/-- The same witness retains the actual named callee's steps for recursive
proofs, independently of how many selections the callee contains. -/
theorem named_at_step {dependencies program block steps count step}
    (witness : @Witness dependencies (.steps 0 (Steps.ofList (program := program) (block := block) steps)) count)
    (earlier later : List (Step dependencies program block))
    (split : steps = earlier ++ step :: later) : Named step := by
  subst steps
  cases step with
  | named event frame body bodyRead boundary finalOrdinary children =>
    obtain ⟨_,⟨current⟩⟩ := step_witness earlier later witness
    cases current with
    | leaf original => cases original
    | selection original _ _ => cases original
    | pair original _ _ => cases original
    | child original nested =>
      cases original
      exact ⟨_,⟨nested⟩⟩
  | _ => exact True.intro

/-- Reuse the original pure action order as ordinary traversal steps. -/
def pureSteps {dependencies program block} : Nodes dependencies program block → Steps dependencies program block
  | .nil => .nil
  | .cons first rest => .cons (.pure first) (pureSteps rest)

theorem pureSteps_ofList {dependencies program block} (actions : List (Node dependencies program block)) :
    pureSteps (Nodes.ofList actions) = Steps.ofList (actions.map Step.pure) := by
  induction actions with
  | nil => rfl
  | cons first rest ih => exact congrArg (Steps.cons (.pure first)) ih

/-- The same selected nodes witness the pure child's literal step list.
The step wrapper introduces no selection and preserves the exact count. -/
theorem pureSteps_witness {dependencies program block ordinal count}
    (actions : List (Node dependencies program block))
    (witness : Witness (.nodes ordinal (Nodes.ofList actions)) count) :
    Nonempty (Witness (.steps ordinal (Steps.ofList (actions.map Step.pure))) count) := by
  induction actions generalizing ordinal count with
  | nil =>
    change Witness (.nodes ordinal .nil) count at witness
    cases witness with
    | leaf original => exact ⟨.leaf rfl⟩
    | selection original _ _ => cases original
    | child original _ => cases original
    | pair original _ _ => cases original
  | cons first rest ih =>
    change Witness (.nodes ordinal (.cons first (Nodes.ofList rest))) count at witness
    cases witness with
    | leaf original => cases original
    | selection original _ _ => cases original
    | child original _ => cases original
    | pair original head tail =>
      cases original
      obtain ⟨shifted⟩ := ih tail
      exact ⟨.pair rfl (.child rfl head) shifted⟩

def PureNamed {dependencies program block} : Step dependencies program block → Prop
  | .pure (.named _ _ _ _ _ nodes) => ∃ count, Nonempty (Witness (.nodes 0 nodes) count)
  | _ => True

/-- Project the exact pure child's occurrence from the outer checked body. -/
theorem pure_named_at_step {dependencies program block steps count step}
    (witness : @Witness dependencies (.steps 0 (Steps.ofList (program := program) (block := block) steps)) count)
    (earlier later : List (Step dependencies program block))
    (split : steps = earlier ++ step :: later) : PureNamed step := by
  subst steps
  cases step
  case pure node =>
    cases node
    case named =>
      obtain ⟨_,⟨current⟩⟩ := step_witness earlier later witness
      cases current with
      | leaf original => cases original
      | selection original _ _ => cases original
      | pair original _ _ => cases original
      | child original nested =>
        cases original
        cases nested with
        | leaf original => cases original
        | selection original _ _ => cases original
        | pair original _ _ => cases original
        | child original inside =>
          cases original
          exact ⟨_,⟨inside⟩⟩
    all_goals exact True.intro
  all_goals exact True.intro

#print axioms pureSteps_witness
#print axioms pure_named_at_step
#print axioms direct_at_step
#print axioms named_at_step
end Qleisli.RuntimeLiteralSelectionWitness
