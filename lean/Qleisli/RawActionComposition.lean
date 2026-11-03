import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimePureComposition

/-! Derived sequential evaluation of the existing independent Raw action.
The actual original step reader and its literal event lists determine every
state transition; the real final output permutation is retained. This proves
physical trace composition, not typed-code/Gram or source preservation, and
makes no bounded scalar-availability or work-equivalence claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RawActionComposition
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite
open QleisliKernel.Qirf
open QleisliKernel.Semantics Qleisli.Semantics

theorem events_append (dependencies : List Dependency) (first rest : List Event) (values : Nat → ℂ) :
    RawAction.events dependencies (first ++ rest) values =
      RawAction.events dependencies rest (RawAction.events dependencies first values) := by
  simp only [RawAction.events,List.foldl_append]

/-- An evaluation helper for the existing trace/action definitions. It does
not check admissibility, build a matrix or grant a native accepted handle. -/
noncomputable def advance (dependencies : List Dependency)
    (state : RawTrace.Interface × (Nat → ℂ)) (operation : Op) : Option (RawTrace.Interface × (Nat → ℂ)) := do
  let (next,emitted) ← RawTrace.step state.1 operation
  return (next,RawAction.events dependencies emitted state.2)

noncomputable def execute (dependencies : List Dependency) (operations : List Op)
    (state : RawTrace.Interface) (values : Nat → ℂ) : Option (RawTrace.Interface × (Nat → ℂ)) :=
  operations.foldlM (advance dependencies) (state,values)

/-- Keep all original event lists, including empty events and structural
changes. Only the mathematical event fold is composed; no bounded event charge
or coefficient operation is reassociated. -/
theorem execute_trace (dependencies : List Dependency) (operations : List Op)
    (prepared : RawTrace.Prepared) (values : Nat → ℂ) :
    execute dependencies operations prepared.state (RawAction.events dependencies prepared.events values) =
      (operations.foldlM RawTrace.advance prepared).map
        (fun result => (result.state,RawAction.events dependencies result.events values)) := by
  induction operations generalizing prepared with
  | nil => rfl
  | cons operation operations ih =>
    cases original : RawTrace.step prepared.state operation with
    | none =>
      simp only [execute,List.foldlM_cons,advance,RawTrace.advance,original,bind,Option.bind,
        Option.map_none]
    | some result =>
      obtain ⟨next,emitted⟩ := result
      simpa only [execute,List.foldlM_cons,advance,RawTrace.advance,original,bind,Option.bind,
        pure,Option.pure_def,events_append] using
        ih {prepared with state := next,events := prepared.events ++ emitted}

/-- The final action is exactly RawTrace.finish's recorded output-wire order.
It cannot be replaced by equal physical widths or a source-owner permutation. -/
noncomputable def finish (dependencies : List Dependency) (body : Program)
    (state : RawTrace.Interface × (Nat → ℂ)) : Nat → ℂ :=
  let wires := body.outputs.flatMap fun token =>
    ((state.1.live.find? (fun port => port.token == token)).map (·.wires)).getD []
  RawAction.event dependencies (.reorder state.1.frame.length (RawTrace.axes state.1 wires)) state.2

theorem program_execute (dependencies : List Dependency) (body : Program) (values : Nat → ℂ) :
    RawAction.program dependencies body values =
      (execute dependencies body.operations (RawTrace.initial body.inputs) values).map (finish dependencies body) := by
  let initial : RawTrace.Prepared :=
    ⟨RawTrace.initial body.inputs,[],(RawTrace.initial body.inputs).frame.length⟩
  have actual := execute_trace dependencies body.operations initial values
  change execute dependencies body.operations (RawTrace.initial body.inputs) values = _ at actual
  rw [actual]
  cases original : body.operations.foldlM RawTrace.advance initial with
  | none => simp only [RawAction.program,RawTrace.run,initial,original,bind,Option.bind,Option.map_none]
  | some result =>
    simp only [RawAction.program,RawTrace.run,initial,original,bind,Option.bind,pure,
      Option.map_some,RawTrace.finish,finish]
    simp only [RawAction.events,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- Grouping retains the same intermediate interfaces and the first missing
operand. This is only the unbounded complex action of the actual Raw steps. -/
theorem execute_chunks (dependencies : List Dependency) (chunks : List (List Op))
    (state : RawTrace.Interface) (values : Nat → ℂ) :
    execute dependencies chunks.flatten state values =
      chunks.foldlM (fun state chunk => execute dependencies chunk state.1 state.2) (state,values) := by
  induction chunks generalizing state values with
  | nil => rfl
  | cons first rest ih =>
    simp only [execute,List.flatten_cons,List.foldlM_append,List.foldlM_cons]
    cases chunkRead : first.foldlM (advance dependencies) (state,values) with
    | none => rfl
    | some next =>
      obtain ⟨nextState,nextValues⟩ := next
      simpa only [execute,bind,Option.bind] using ih nextState nextValues

/-- Actual checked source intervals compose the SAME original pure Raw root,
including its real final permutation, on every joint reference slice. The
local typed forest-code/action/Gram obligations are not assumed or discharged. -/
theorem prepared_action {Reference : Type}
    {artifact root owner name signature body request initial checked}
    (composition : @RuntimePureComposition.Prepared artifact root owner name signature body request initial checked)
    (joint : Nat → Reference → ℂ) (reference : Reference) :
    RawAction.program root.dependencies composition.raw (fun input => joint input reference) =
      ((checked.result.actions.map RuntimePureComposition.operations).foldlM
        (fun state chunk => execute root.dependencies chunk state.1 state.2)
        (RawTrace.initial composition.raw.inputs,fun input => joint input reference)).map
          (finish root.dependencies composition.raw) := by
  rw [program_execute,composition.operations]
  have grouped := execute_chunks root.dependencies
    (checked.result.actions.map RuntimePureComposition.operations)
    (RawTrace.initial composition.raw.inputs) (fun input => joint input reference)
  simpa only [List.flatMap_def] using
    congrArg (fun result => result.map (finish root.dependencies composition.raw)) grouped

#print axioms execute_trace
#print axioms program_execute
#print axioms prepared_action

end Qleisli.RawActionComposition
