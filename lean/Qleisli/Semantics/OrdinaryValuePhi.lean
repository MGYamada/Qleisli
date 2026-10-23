import QleisliKernel.Semantics.OrdinaryValueTransport
import Qleisli.Semantics.OrdinaryValue

/-! New ordinary output trees from actual Raw phis.
All phi operands are read from the same incoming history. The tree relation is
structural, and its leaf lookup premise is proved from the actual merged and
phiBindings definitions, fresh outputs and unique phi destinations. No source
body faithfulness, native acceptance or successful solver premise is assumed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue
open RawInstrument

/-- One literal edge from the selected operand of an actual phi to its output.
This relation has no value or Represents claim in its definition. -/
def PhiEdge (choice : Bool) (phis : List Observation.ClassicalPhi)
    (source target : Nat) : Prop :=
  ∃ phi ∈ phis, (if choice then phi.thenId else phi.elseId) = source ∧ phi.output = target

private theorem lookup_cons_same (id : Nat) (bit : Bool) (rest : Valuation) :
    lookup ((id,bit) :: rest) id = some bit := by
  simp [lookup,List.find?]

private theorem lookup_cons_other (first id : Nat) (bit : Bool) (rest : Valuation)
    (different : first ≠ id) : lookup ((first,bit) :: rest) id = lookup rest id := by
  have unequal : (first == id) = false := beq_eq_false_iff_ne.mpr different
  simp [lookup,List.find?,unequal]

private theorem lookup_append_absent (before added : Valuation) (id : Nat)
    (fresh : lookup before id = none) : lookup (before ++ added) id = lookup added id := by
  unfold lookup at fresh ⊢
  rw [List.find?_append]
  cases found : before.find? (fun pair => pair.1 == id) with
  | none => simp
  | some pair => simp [found] at fresh

private theorem phiBindings_cons (choice : Bool) (phi : Observation.ClassicalPhi)
    (phis : List Observation.ClassicalPhi) (before : Valuation) :
    phiBindings choice (phi :: phis) before = (do
      let bit ← lookup before (if choice then phi.thenId else phi.elseId)
      let rest ← phiBindings choice phis before
      pure ((phi.output,bit) :: rest)) := by
  cases selected : RawInstrument.value before (if choice then phi.thenId else phi.elseId) <;>
    simp [phiBindings,List.mapM_cons,lookup_actual,selected]

/-- A successful actual phi list returns the selected incoming value at each
unique output. Duplicate source operands are deliberately allowed. -/
theorem phiBindings_lookup {choice : Bool} {phis : List Observation.ClassicalPhi}
    {before added : Valuation} (evaluated : phiBindings choice phis before = some added)
    (unique : (phis.map Observation.ClassicalPhi.output).Nodup)
    {phi : Observation.ClassicalPhi} (member : phi ∈ phis) :
    lookup added phi.output = lookup before (if choice then phi.thenId else phi.elseId) := by
  induction phis generalizing added with
  | nil => simp at member
  | cons head tail ih =>
    rw [phiBindings_cons] at evaluated
    cases selected : lookup before (if choice then head.thenId else head.elseId) with
    | none => simp [selected] at evaluated
    | some bit =>
      cases rest : phiBindings choice tail before with
      | none => simp [selected,rest] at evaluated
      | some extra =>
        have same : (head.output,bit) :: extra = added := by simpa [selected,rest] using evaluated
        subst added
        have distinct : head.output ∉ tail.map Observation.ClassicalPhi.output :=
          (List.nodup_cons.mp unique).1
        have tailUnique : (tail.map Observation.ClassicalPhi.output).Nodup :=
          (List.nodup_cons.mp unique).2
        rcases List.mem_cons.mp member with equal | member
        · subst phi
          rw [lookup_cons_same,selected]
        · have different : head.output ≠ phi.output := by
            intro equal
            apply distinct
            rw [equal]
            exact List.mem_map_of_mem member
          rw [lookup_cons_other head.output phi.output bit extra different]
          exact ih rest tailUnique member

/-- The generic leaf premise follows from the actual merge, rather than being
an assumed output-value correspondence. This only states dynamic value freshness;
lexical/global source authorization remains the existing separate Raw duty. -/
theorem merged_lookup_along (before after : History) (choice : Bool)
    (phis : List Observation.ClassicalPhi)
    (merged : RawInstrument.merged choice phis before = some after)
    (fresh : ∀ phi ∈ phis, lookup before.values phi.output = none)
    (unique : (phis.map Observation.ClassicalPhi.output).Nodup) :
    LookupAlong (PhiEdge choice phis) before.values after.values := by
  rw [merged_actual] at merged
  cases bindings : phiBindings choice phis before.values with
  | none => simp [bindings] at merged
  | some added =>
    simp only [bindings,Option.map_some,Option.some.injEq] at merged
    subst after
    intro source target edge bit present
    obtain ⟨phi,member,selected,output⟩ := edge
    subst source
    subst target
    change lookup (before.values ++ added) phi.output = some bit
    rw [lookup_append_absent before.values added phi.output (fresh phi member)]
    rw [phiBindings_lookup bindings unique member]
    exact present

/-- A complete selected-arm ordinary tree is moved to the actual simultaneous
phi outputs without changing its logical value, nominal type, range or shape.
The hidden outcomes and full quantum operator are the original ones. The
structural edge premise is an explicit obligation on the proposed output tree;
this theorem does not authenticate that tree against an original source body. -/
theorem merged_transports {basis : FiniteCarrier.Basis} {logical : Value}
    {source target : Storage} (before after : History)
    (choice : Bool) (phis : List Observation.ClassicalPhi)
    (represented : Represents before.values basis logical source)
    (moved : StorageTransport (PhiEdge choice phis) source target)
    (merged : RawInstrument.merged choice phis before = some after)
    (fresh : ∀ phi ∈ phis, lookup before.values phi.output = none)
    (unique : (phis.map Observation.ClassicalPhi.output).Nodup) :
    Represents after.values basis logical target ∧
      after.hidden = before.hidden ∧ after.operator = before.operator := by
  have old := merged_preserves before after choice phis represented merged
  exact ⟨represented.transport (merged_lookup_along before after choice phis merged fresh unique) moved,
    old.2.1,old.2.2⟩

/-- Ordinary branch lowering can retain an existing identity when both arm
results name that same SSA value. Other leaves must be actual selected phi edges.
This disjunction changes no nominal or structural transport rule. -/
def KeptOrPhiEdge (choice : Bool) (phis : List Observation.ClassicalPhi)
    (source target : Nat) : Prop := source = target ∨ PhiEdge choice phis source target

/-- Actual merge preserves every incoming binding, including bindings used
unchanged in a mixed tree. This is derived from actual append semantics. -/
theorem merged_extends (before after : History) (choice : Bool)
    (phis : List Observation.ClassicalPhi)
    (merged : RawInstrument.merged choice phis before = some after) :
    Extends before.values after.values := by
  rw [merged_actual] at merged
  cases bindings : phiBindings choice phis before.values with
  | none => simp [bindings] at merged
  | some added =>
    simp only [bindings,Option.map_some,Option.some.injEq] at merged
    subst after
    exact append_extends before.values added

/-- Identity leaves use proven old-binding preservation. Renamed leaves use
actual simultaneous phi lookup; neither branch assumes a target representation. -/
theorem merged_kept_lookup_along (before after : History) (choice : Bool)
    (phis : List Observation.ClassicalPhi)
    (merged : RawInstrument.merged choice phis before = some after)
    (fresh : ∀ phi ∈ phis, lookup before.values phi.output = none)
    (unique : (phis.map Observation.ClassicalPhi.output).Nodup) :
    LookupAlong (KeptOrPhiEdge choice phis) before.values after.values := by
  have kept := merged_extends before after choice phis merged
  have renamed := merged_lookup_along before after choice phis merged fresh unique
  intro source target edge bit present
  rcases edge with same | actualPhi
  · subst target
    exact kept source bit present
  · exact renamed source target actualPhi bit present

/-- A complete ordinary tree may combine unchanged IDs with fresh actual phi
outputs. Equal IDs allow ordinary reuse, never arbitrary renaming. All original
shape, origin, field-order, range and hidden/operator obligations are retained.
The relation does not authenticate the compiler's choice of the source tree. -/
theorem merged_transports_kept {basis : FiniteCarrier.Basis} {logical : Value}
    {source target : Storage} (before after : History)
    (choice : Bool) (phis : List Observation.ClassicalPhi)
    (represented : Represents before.values basis logical source)
    (moved : StorageTransport (KeptOrPhiEdge choice phis) source target)
    (merged : RawInstrument.merged choice phis before = some after)
    (fresh : ∀ phi ∈ phis, lookup before.values phi.output = none)
    (unique : (phis.map Observation.ClassicalPhi.output).Nodup) :
    Represents after.values basis logical target ∧
      after.hidden = before.hidden ∧ after.operator = before.operator := by
  have old := merged_preserves before after choice phis represented merged
  exact ⟨represented.transport (merged_kept_lookup_along before after choice phis merged fresh unique) moved,
    old.2.1,old.2.2⟩

end Qleisli.Semantics.OrdinaryValue
