import Qleisli.HierarchicalCircuitTrace

/-! Actual artifact evaluation for freshly constructed circuit traces.
Only evaluations of independently requested actual atoms are premises. The
remaining circuit is reconstructed from its real bodies and dependencies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.HierarchicalCircuitTrace
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalSemantics HierarchicalFiniteEvaluation
open scoped Matrix

theorem project_cases (atoms : Array CircuitTrace.Atom) (index : Nat) (d : Definition)
    (node : CircuitTrace.Node) (found : CircuitTrace.project atoms index d = some node) :
    (∃ atom ∈ atoms.toList, atom.index = index ∧ atom.interface = d.interface ∧
      node = ⟨.atom index,[]⟩) ∨
    (∃ wiring, Wiring.project d = some wiring ∧ node = ⟨ofWiring wiring.operation,wiring.children⟩) := by
  unfold CircuitTrace.project at found
  cases chosen : atoms.find? (fun atom => atom.index == index) with
  | some atom =>
    simp only [chosen] at found
    split at found
    next matched =>
      exact Or.inl ⟨atom,by simpa using Array.mem_of_find?_eq_some chosen,
        by simpa using Array.find?_some chosen,by simpa using matched,(Option.some.inj found).symm⟩
    next mismatched => contradiction
  | none =>
    simp only [chosen] at found
    cases projected : Wiring.project d with
    | none => simp [projected,bind,Option.bind] at found
    | some wiring =>
      simp only [projected,bind,Option.bind,pure] at found
      exact Or.inr ⟨wiring,rfl,(Option.some.inj found).symm⟩

/-- Trace validity follows from this same fresh derivation, including children
that occur repeatedly in the schedule. It is never a producer-supplied flag. -/
theorem derives_valid (artifact : Artifact) (atoms : Array CircuitTrace.Atom)
    (index : Nat) (trace : CircuitTrace.Trace) (derived : CircuitTrace.Derives artifact atoms index trace) :
    CircuitTrace.valid trace.width trace = true := by
  cases derived with
  | node index d cache trace found children computed =>
    obtain ⟨_,_,_,_,_,_,_,_,checked⟩ := CircuitTrace.summarize_fields atoms cache index d trace computed
    have size : trace.width = (wires d.interface.inputs).size := by
      simp only [CircuitTrace.valid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at checked
      exact checked.1.1.2
    simpa only [size] using checked

private theorem mapped_valid (read : Nat → Option CircuitTrace.Trace)
    (ready : ∀ index trace, read index = some trace → CircuitTrace.valid trace.width trace = true)
    (indices : List Nat) (traces : List CircuitTrace.Trace)
    (computed : indices.mapM read = some traces) :
    ∀ trace ∈ traces, CircuitTrace.valid trace.width trace = true := by
  induction indices generalizing traces with
  | nil =>
    have same : traces = [] := by simpa using computed.symm
    simp [same]
  | cons index rest ih =>
    cases first : read index with
    | none => simp [List.mapM_cons,first] at computed
    | some value =>
      cases tail : rest.mapM read with
      | none => simp [List.mapM_cons,first,tail] at computed
      | some values =>
        have same : traces = value::values := by simpa [List.mapM_cons,first,tail] using computed.symm
        subst traces
        intro trace member
        rcases List.mem_cons.mp member with rfl | inside
        · exact ready index trace first
        · exact ih values tail trace inside

/-- Only the explicitly requested actual atoms may be supplied as premises.
Every premise refers to the same artifact and its full requested interface. -/
def AtomEquations (leaves : Leaves Operator) (artifact : Artifact)
    (atoms : Array CircuitTrace.Atom) (operations : Nat → Operator) : Prop :=
  ∀ atom ∈ atoms.toList, ∃ fuel,
    physical algebra leaves artifact fuel atom.index = some (operations atom.index) ∧
      (operations atom.index).inputWidth = width atom.interface.inputs ∧
      (operations atom.index).outputWidth = width atom.interface.outputs

theorem children_evaluate (leaves : Leaves Operator) (artifact : Artifact) (atoms : Nat → Operator) (cache : CircuitTrace.Cache)
    (ready : ∀ index code, (cache[index]?).bind id = some code →
      ∃ fuel op, physical algebra leaves artifact fuel index = some op ∧ At atoms code op)
    (indices : List Nat) (codes : List CircuitTrace.Trace)
    (computed : indices.mapM (fun i => (cache[i]?).bind id) = some codes) :
    ∃ fuel ops, indices.mapM (physical algebra leaves artifact fuel) = some ops ∧
      List.Forall₂ (fun code op => At atoms code op) codes ops := by
  induction indices generalizing codes with
  | nil =>
    have same : codes = [] := by simpa using computed.symm
    subst codes
    exact ⟨0,[],rfl,.nil⟩
  | cons index rest ih =>
    rw [List.mapM_cons] at computed
    change (((cache[index]?).bind id).bind (fun code =>
      (rest.mapM (fun i => (cache[i]?).bind id)).bind (fun tail => some (code::tail)))) = some codes at computed
    cases lookup : (cache[index]?).bind id with
    | none => simp only [lookup,Option.bind_none] at computed; contradiction
    | some code =>
      rw [lookup] at computed
      simp only [Option.bind_some] at computed
      cases tail : rest.mapM (fun i => (cache[i]?).bind id) with
      | none => simp only [tail,Option.bind_none] at computed; contradiction
      | some following =>
        have same : codes = code::following := by
          simpa only [tail,Option.bind_some,Option.some.injEq] using computed.symm
        subst codes
        obtain ⟨firstFuel,op,first,firstAt⟩ := ready index code lookup
        obtain ⟨tailFuel,ops,following,followingAt⟩ := ih _ tail
        let fuel := firstFuel+tailFuel
        have firstMore := evaluate_more algebra (definition leaves artifact) firstFuel index op first fuel (by dsimp [fuel]; omega)
        change HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some op at firstMore
        have tailMore := HierarchicalEvaluation.mapM_congr_success rest
          (physical algebra leaves artifact tailFuel) (physical algebra leaves artifact fuel) ops following
          (fun child _ value evaluated =>
            evaluate_more algebra (definition leaves artifact) tailFuel child value evaluated fuel (by dsimp [fuel]; omega))
        exact ⟨fuel,op::ops,by simp only [List.mapM_cons,firstMore,tailMore,bind,Option.bind,pure],
          .cons firstAt followingAt⟩


theorem derives_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (atoms : Array CircuitTrace.Atom) (operations : Nat → Operator)
    (atomEquations : AtomEquations leaves artifact atoms operations)
    (index : Nat) (trace : CircuitTrace.Trace)
    (derived : CircuitTrace.Derives artifact atoms index trace) :
    ∃ fuel op, physical algebra leaves artifact fuel index = some op ∧ At operations trace op := by
  induction derived with
  | node index d cache trace found children computed ih =>
    obtain ⟨node,traces,projected,cached,evaluated,_,_,widths,valid⟩ :=
      CircuitTrace.summarize_fields atoms cache index d trace computed
    rcases project_cases atoms index d node projected with
      ⟨atom,member,atomIndex,header,nodeEq⟩ | ⟨wiring,wireFound,nodeEq⟩
    · subst node
      have empty : traces = [] := by simpa using cached.symm
      subst traces
      have same : trace = CircuitTrace.atomic index (width d.interface.inputs) := by
        simpa [CircuitTrace.eval,width] using evaluated.symm
      subst trace
      obtain ⟨fuel,actual,inputs,outputs⟩ := atomEquations atom member
      rw [atomIndex] at actual inputs outputs
      rw [header] at inputs outputs
      refine ⟨fuel,operations index,actual,inputs,outputs.trans widths,?_⟩
      exact (meaning_atomic operations (width d.interface.inputs) index).symm
    · subst node
      obtain ⟨fuel,ops,actual,ready⟩ :=
        children_evaluate leaves artifact operations cache ih wiring.children traces cached
      have validChildren := mapped_valid (fun i => (cache[i]?).bind id)
        (fun i t h => derives_valid artifact atoms i t (children i t h)) wiring.children traces cached
      have result := eval_at operations d.interface (width d.interface.inputs) wiring.operation
        traces ops trace ready validChildren rfl widths evaluated valid
      refine ⟨fuel+1,apply d.interface (HierarchicalWiring.tag wiring.operation) ops,?_,result⟩
      rw [physical_step algebra leaves artifact fuel index d
        (HierarchicalWiring.tag wiring.operation) wiring.children found
        (HierarchicalWiring.project_code d wiring wireFound),actual]
      rfl

/-- A fresh inspector result denotes exactly its derived phase-sensitive trace.
Only the explicitly selected actual atom equations remain conditional. -/
theorem inspect_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (atoms : Array CircuitTrace.Atom) (operations : Nat → Operator)
    (atomEquations : AtomEquations leaves artifact atoms operations)
    (order : Array Nat) (remaining : Nat) (state : CircuitTrace.State)
    (index : Nat) (trace : CircuitTrace.Trace)
    (accepted : CircuitTrace.inspect artifact atoms order remaining = .ok state)
    (found : (state.cache[index]?).bind id = some trace) :
    ∃ fuel op, physical algebra leaves artifact fuel index = some op ∧ At operations trace op := by
  exact derives_evaluates leaves artifact atoms operations atomEquations index trace
    ((CircuitTrace.inspect_sound artifact atoms order remaining state accepted).1 index trace found)

end Qleisli.HierarchicalCircuitTrace
