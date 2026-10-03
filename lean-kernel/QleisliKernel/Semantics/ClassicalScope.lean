import QleisliKernel.Semantics.Observation

/-! Independent classical SSA and lexical-scope rules for original raw programs.
The judgment neither imports a verifier nor assumes a supplied verification
result. Every phi operand is resolved before any phi destination is introduced.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.ClassicalScope
open Observation

structure State where
  issued : List (Nat × Nat) := []
  active : List Nat := [0]
  current : Nat := 0
  next : Nat := 1
  deriving Repr

def Visible (state : State) (value : Nat) : Prop :=
  ∃ scope, (value,scope) ∈ state.issued ∧ scope ∈ state.active

def ArmVisible (state : State) (arm value : Nat) : Prop :=
  ∃ scope, (value,scope) ∈ state.issued ∧ (scope = arm ∨ scope ∈ state.active)

/-- Issued identities include inaccessible prior arms. Leaving a scope never
makes one of its names available for a second definition. -/
structure Insert (before : State) (value : Nat) (after : State) : Prop where
  fresh : value ∉ before.issued.map Prod.fst
  result : after = {before with issued := before.issued ++ [(value,before.current)]}

inductive Inserts : State → List Nat → State → Prop
  | nil (state) : Inserts state [] state
  | cons (before value middle rest after) (head : Insert before value middle)
      (tail : Inserts middle rest after) : Inserts before (value :: rest) after

def enter (state : State) : State :=
  {state with active := state.active ++ [state.next],current := state.next,next := state.next + 1}

def leave (parent arm : Nat) (state : State) : State :=
  {state with active := state.active.filter (· != arm),current := parent}

/-- Phi inputs belong to their own completed arm or the enclosing lexical
environment. Destinations cannot satisfy another phi's operand obligation. -/
def Phis (state : State) (left right : Nat) (phis : List ClassicalPhi) : Prop :=
  ∀ phi ∈ phis, ArmVisible state left phi.thenId ∧ ArmVisible state right phi.elseId

mutual
  inductive Step : State → Observation.Op → State → Prop
    | pure (state op) : Step state (.pure op) state
    | measure (before input output after) (fresh : Insert before output after) :
        Step before (.measure input output) after
    | reset (state input output wire) : Step state (.reset input output wire) state
    | discard (state input) : Step state (.discard input) state
    | constant (before value output after) (fresh : Insert before output after) :
        Step before (.constant value output) after
    | not (before input output after) (access : Visible before input)
        (fresh : Insert before output after) : Step before (.not input output) after
    | xor (before left right output after) (a : Visible before left) (b : Visible before right)
        (fresh : Insert before output after) : Step before (.xor left right output) after
    | and (before left right output after) (a : Visible before left) (b : Visible before right)
        (fresh : Insert before output after) : Step before (.and left right output) after
    | branch (before condition thenOps elseOps quantum classical left right after)
        (access : Visible before condition)
        (thenArm : Run (enter before) thenOps left)
        (elseArm : Run (enter (leave before.current before.next left)) elseOps right)
        (operands : Phis (leave before.current (leave before.current before.next left).next right)
          before.next (leave before.current before.next left).next classical)
        (destinations : Inserts (leave before.current (leave before.current before.next left).next right)
          (classical.map ClassicalPhi.output) after) :
        Step before (.branch condition thenOps elseOps quantum classical) after
  inductive Run : State → List Observation.Op → State → Prop
    | nil (state) : Run state [] state
    | cons (before op middle ops after) (head : Step before op middle)
        (tail : Run middle ops after) : Run before (op :: ops) after
end

/-- Ordinary input, every use/definition in both branches, and every returned
classical value obey lexical SSA. This is independent of quantum ownership,
effect denotation, numerical execution and any optional algorithm request. -/
def ScopeSafe (program : Observation.Program) : Prop :=
  ∃ initial final, Inserts {} program.classicalInputs initial ∧
    Run initial program.operations final ∧ ∀ value ∈ program.classicalOutputs, Visible final value

theorem Insert.issued {before after : State} {value : Nat} (step : Insert before value after) :
    before.issued.Sublist after.issued := by
  rw [step.result]
  exact List.sublist_append_left _ _

theorem Insert.distinct {before after : State} {value : Nat} (step : Insert before value after)
    (distinct : (before.issued.map Prod.fst).Nodup) : (after.issued.map Prod.fst).Nodup := by
  rw [step.result,List.map_append]
  simp only [List.map_cons,List.map_nil,List.nodup_append]
  refine ⟨distinct,by simp,?_⟩
  intro old member new singleton same
  have chosen : new = value := by simpa using singleton
  exact step.fresh ((same.trans chosen) ▸ member)

theorem Inserts.distinct {before after : State} {values : List Nat} (steps : Inserts before values after)
    (distinct : (before.issued.map Prod.fst).Nodup) : (after.issued.map Prod.fst).Nodup := by
  induction steps with
  | nil state => exact distinct
  | cons before value middle rest after head tail ih => exact ih (head.distinct distinct)

mutual
  theorem Step.distinct {before after : State} {op : Observation.Op} (step : Step before op after)
      (distinct : (before.issued.map Prod.fst).Nodup) : (after.issued.map Prod.fst).Nodup := by
    cases step with
    | pure state op => exact distinct
    | measure before input output after fresh => exact fresh.distinct distinct
    | reset state input output wire => exact distinct
    | discard state input => exact distinct
    | constant before value output after fresh => exact fresh.distinct distinct
    | not before input output after access fresh => exact fresh.distinct distinct
    | xor before left right output after a b fresh => exact fresh.distinct distinct
    | and before left right output after a b fresh => exact fresh.distinct distinct
    | branch before condition thenOps elseOps quantum classical left right after access thenArm elseArm operands destinations =>
      exact destinations.distinct (elseArm.distinct (thenArm.distinct distinct))
  theorem Run.distinct {before after : State} {ops : List Observation.Op} (run : Run before ops after)
      (distinct : (before.issued.map Prod.fst).Nodup) : (after.issued.map Prod.fst).Nodup := by
    cases run with
    | nil state => exact distinct
    | cons before op middle ops after head tail => exact tail.distinct (head.distinct distinct)
end

/-- Complete scope safety implies global SSA uniqueness, including values
issued in arms that are inaccessible at return. -/
theorem ScopeSafe.unique {program : Observation.Program} (safe : ScopeSafe program) :
    ∃ initial final, Inserts {} program.classicalInputs initial ∧
      Run initial program.operations final ∧ (final.issued.map Prod.fst).Nodup ∧
      ∀ value ∈ program.classicalOutputs, Visible final value := by
  obtain ⟨initial,final,inputs,run,outputs⟩ := safe
  exact ⟨initial,final,inputs,run,run.distinct (inputs.distinct (by simp)),outputs⟩

namespace Examples

private def initial : State := ⟨[(0,0)],[0],0,1⟩
private def left : State := ⟨[(0,0),(1,1)],[0,1],1,2⟩
private def right : State := ⟨[(0,0),(1,1),(2,2)],[0,2],2,3⟩
private def merged : State := leave 0 2 right
private def final : State := ⟨[(0,0),(1,1),(2,2),(3,0)],[0],0,3⟩

/-- A left-arm value is inaccessible in the right arm even though its identity
is still issued; attempting to redefine that identity is also prohibited. -/
theorem exclusive_arm :
    ¬ Visible (enter (leave 0 1 left)) 1 ∧
      ∀ after, ¬ Insert (enter (leave 0 1 left)) 1 after := by
  constructor
  · simp [Visible,enter,leave,left]
  · intro after issued
    have fresh := issued.fresh
    simp [enter,leave,left] at fresh

/-- A phi destination does not become an operand for another simultaneous phi. -/
theorem phi_operands_before_outputs : ¬ Phis merged 1 2 [⟨1,2,3⟩,⟨3,3,4⟩] := by
  intro phis
  have future := (phis ⟨3,3,4⟩ (by simp)).1
  simp [ArmVisible,merged,leave,right] at future

/-- Duplicate external classical inputs are invalid before any operation runs. -/
theorem duplicate_input (after : State) : ¬ Inserts {} [7,7] after := by
  intro inputs
  cases inputs with
  | cons before value middle rest after first tail =>
    cases tail with
    | cons before value middle rest after second tail =>
      have fresh := second.fresh
      rw [first.result] at fresh
      simp at fresh

/-- A complete accepted-shaped reference program uses both lexical arms and
returns their explicit phi. This proof is independent of verifier execution. -/
theorem two_arm_phi : ScopeSafe
    ⟨[],[0],[.branch 0 [.constant true 1] [.constant false 2] [] [⟨1,2,3⟩]],[],[3],.unitary⟩ := by
  refine ⟨initial,final,.cons _ _ _ _ _ ⟨by simp,rfl⟩ (.nil _),?_,?_⟩
  · refine .cons _ _ _ _ _ ?_ (.nil _)
    refine .branch _ _ _ _ _ _ left right _ ?_ ?_ ?_ ?_ ?_
    · exact ⟨0,by simp [initial],by simp [initial]⟩
    · exact .cons _ _ _ _ _ (.constant _ _ _ _ ⟨by simp [enter,initial],rfl⟩) (.nil _)
    · exact .cons _ _ _ _ _ (.constant _ _ _ _ ⟨by simp [enter,leave,left],rfl⟩) (.nil _)
    · intro phi member
      have same : phi = ⟨1,2,3⟩ := by simpa using member
      subst phi
      exact ⟨⟨1,by simp [leave,right],Or.inl rfl⟩,⟨2,by simp [leave,right],Or.inl rfl⟩⟩
    · exact .cons _ _ _ _ _ ⟨by simp [leave,right],rfl⟩ (.nil _)
  · intro value member
    have same : value = 3 := by simpa using member
    subst value
    exact ⟨0,by simp [final],by simp [final]⟩

end Examples

end QleisliKernel.Semantics.ClassicalScope
