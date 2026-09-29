import QleisliKernel.Hierarchical.NodeTyping

/-! Untrusted call expansion into existing rewire and sequence nodes.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This producer issues no evidence and adds no acceptance rule. Its output must
pass the ordinary independent checker; input-call typing remains an explicit
premise of translation preservation. The child is referenced, never copied. -/

namespace QleisliKernel.Hierarchical.CallLowering
open Artifact

structure Plan where
  before : Definition
  after : Definition
  replacement : Definition
  deriving Repr

def build (parent callee : Definition) (child first last : Nat)
    (input output : PortMap) : Plan :=
  {before := ⟨⟨parent.interface.inputs,callee.interface.inputs⟩,.unitary,.rewire input⟩
   after := ⟨⟨callee.interface.outputs,parent.interface.outputs⟩,.unitary,.rewire output⟩
   replacement := ⟨parent.interface,parent.effect,.sequence #[first,child,last]⟩}

/-- Appended indices are derived from the actual table, not proposed metadata.
Checking capacities, call typing, graph scheduling and evidence is mandatory
before a caller may use the expanded artifact as a verified translation. -/
def plan (artifact : Artifact) (index : Nat) : Option Plan := do
  let parent ← artifact.definitions[index]?
  let .call child input output := parent.body | none
  let callee ← artifact.definitions[child]?
  return build parent callee child artifact.definitions.size (artifact.definitions.size+1) input output

/-- Only the definition table is changed. Proofs/meanings are deliberately not
manufactured from implementation data; an independent contract must bind them. -/
def install (artifact : Artifact) (index : Nat) (expansion : Plan) : Artifact :=
  {artifact with definitions :=
    ((artifact.definitions.setIfInBounds index expansion.replacement).push expansion.before).push expansion.after}

theorem plan_binding (artifact : Artifact) (index : Nat) (expansion : Plan)
    (produced : plan artifact index = some expansion) :
    ∃ parent callee child input output,
      artifact.definitions[index]? = some parent ∧
      parent.body = .call child input output ∧
      artifact.definitions[child]? = some callee ∧
      expansion = build parent callee child artifact.definitions.size
        (artifact.definitions.size+1) input output := by
  cases hp : artifact.definitions[index]? with
  | none => simp [plan,hp] at produced
  | some parent =>
    cases hb : parent.body <;> simp [plan,hp,hb] at produced
    next child input output =>
      cases hc : artifact.definitions[child]? with
      | none => simp [hc] at produced
      | some callee =>
        have same : build parent callee child artifact.definitions.size
            (artifact.definitions.size+1) input output = expansion := by simpa [hc] using produced
        exact ⟨parent,callee,child,input,output,rfl,hb,hc,same.symm⟩

theorem install_tables (artifact : Artifact) (index : Nat) (expansion : Plan) :
    (install artifact index expansion).meanings = artifact.meanings ∧
    (install artifact index expansion).encodings = artifact.encodings ∧
    (install artifact index expansion).proofs = artifact.proofs ∧
    (install artifact index expansion).entry = artifact.entry := ⟨rfl,rfl,rfl,rfl⟩

theorem install_size (artifact : Artifact) (index : Nat) (expansion : Plan) :
    (install artifact index expansion).definitions.size = artifact.definitions.size + 2 := by
  simp [install,Nat.add_assoc]

/-- Existing children keep their exact bodies and table indices. In particular,
the producer does not copy a repeated body or replace its literal count. -/
theorem install_other (artifact : Artifact) (index other : Nat) (expansion : Plan)
    (inside : other < artifact.definitions.size) (different : index ≠ other) :
    (install artifact index expansion).definitions[other]? = artifact.definitions[other]? := by
  change (((artifact.definitions.setIfInBounds index expansion.replacement).push
    expansion.before).push expansion.after)[other]? = _
  simp only [Array.getElem?_push,Array.size_push,Array.size_setIfInBounds]
  rw [if_neg (by omega),if_neg (Nat.ne_of_lt inside),Array.getElem?_setIfInBounds_ne different]

/-- Complete input/output permutations and the cross-endpoint fresh renaming
are obtained from actual call typing. Individually valid maps alone do not
justify a call whose two sides rename the same identity inconsistently. -/
theorem typed_maps (artifact : Artifact) (parent callee : Definition)
    (child : Nat) (input output : PortMap)
    (body : parent.body = .call child input output)
    (found : artifact.definitions[child]? = some callee)
    (typed : NodeTyping.conditions artifact parent = true) :
    Ports.shapeValid parent.interface.inputs callee.interface.inputs input = true ∧
    Ports.shapeValid callee.interface.outputs parent.interface.outputs output = true ∧
    NodeTyping.renamed parent.interface callee.interface input output = true := by
  simp only [NodeTyping.conditions,body,found,bind,Option.bind,pure,Option.getD_some,
    Bool.and_eq_true] at typed
  exact ⟨typed.2.1.1.2,typed.2.1.2,typed.2.2⟩

end QleisliKernel.Hierarchical.CallLowering
