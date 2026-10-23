import Qleisli.Semantics.OrdinaryValuePhi

/-! Counterexamples and positive controls for actual Raw phi values and ordinary
storage trees. These establish neither native acceptance nor source replay.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue.PhiExamples
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue

/-- The false arm selects 1, not the producer's preferred input 0. -/
theorem wrong_arm_actual_values :
    phiBindings false [⟨0,1,3⟩] [(0,false),(1,true)] = some [(3,true)] := rfl

theorem wrong_arm_not_false :
    ¬ Represents [(0,false),(1,true),(3,true)] [.bit] (.bit false) (.bit 3) := by
  intro represented
  cases represented with
  | bit id bit present => simp [lookup,List.find?] at present

/-- Raw merge itself can produce duplicate destinations. The first binding
wins, so success alone is insufficient for the per-phi lookup theorem. -/
theorem duplicate_output_actual_values :
    phiBindings true [⟨0,0,2⟩,⟨1,1,2⟩] [(0,false),(1,true)] =
      some [(2,false),(2,true)] := rfl

theorem duplicate_output_masks_second :
    lookup [(0,false),(1,true),(2,false),(2,true)] 2 = some false := rfl

theorem duplicate_output_is_not_unique : ¬ ([2,2] : List Nat).Nodup := by decide

/-- All operands are incoming, even when an earlier phi writes that ID. -/
theorem chain_phi_is_not_simultaneous_input :
    phiBindings true [⟨0,0,2⟩,⟨2,2,3⟩] [(0,false)] = none := rfl

/-- Even the universally permissive leaf relation cannot remove a Unit child. -/
theorem missing_zero_width_node :
    ¬ StorageTransport (fun _ _ => True) (.pair .unit (.bit 0)) (.bit 2) := by
  intro moved
  cases moved

private def empty : FiniteCarrier.Origin := ⟨"demo","Empty","struct Empty {}"⟩
private def wrapper : FiniteCarrier.Origin :=
  ⟨"demo","Wrapper","struct Wrapper { empty: Empty, tag: Bit }"⟩

theorem empty_record_is_not_unit :
    ¬ StorageTransport (fun _ _ => True) (.record empty []) .unit := by
  intro moved
  cases moved

theorem missing_zero_width_field :
    ¬ FieldsTransport (fun _ _ => True)
      [("empty",.record empty []),("tag",.bit 0)] [("tag",.bit 2)] := by
  intro moved
  have names := moved.names
  simp at names

/-- A retained zero-width field needs no phi, but its complete node survives. -/
theorem complete_field_tree : StorageTransport (PhiEdge true [⟨0,1,2⟩])
    (.record wrapper [("empty",.record empty []),("tag",.bit 0)])
    (.record wrapper [("empty",.record empty []),("tag",.bit 2)]) := by
  refine .record wrapper _ _ (.cons "empty" _ _ _ _ (.record empty [] [] .nil) ?_)
  refine .cons "tag" _ _ [] [] (.bit 0 2 ?_) .nil
  exact ⟨⟨0,1,2⟩,by simp,rfl,rfl⟩

/-- Distinct outputs may read the same incoming ordinary bit. -/
theorem copy_source_actual_values :
    phiBindings true [⟨0,1,2⟩,⟨0,1,3⟩] [(0,false),(1,true)] =
      some [(2,false),(3,false)] := rfl

/-- Unique phi destinations alone do not prevent an incoming value from
shadowing the appended result. The fresh-output premise is essential. -/
theorem incoming_output_collision :
    phiBindings true [⟨1,1,0⟩] [(0,false),(1,true)] = some [(0,true)] := rfl

theorem incoming_output_remains_first :
    lookup [(0,false),(1,true),(0,true)] 0 = some false := rfl

/-- End-to-end application to the actual merge. The complete empty
field remains before the Bit field for any hidden history and quantum operator. -/
theorem actual_record_output (before : RawInstrument.History)
    (values : before.values = [(0,false),(1,true)]) :
    ∃ after, RawInstrument.merged true [⟨0,1,2⟩] before = some after ∧
      Represents after.values [.record wrapper ["empty","tag"],.record empty [],.bit]
        (.record wrapper [("empty",.record empty []),("tag",.bit false)])
        (.record wrapper [("empty",.record empty []),("tag",.bit 2)]) ∧
      after.hidden = before.hidden ∧ after.operator = before.operator := by
  let after : RawInstrument.History := {before with values := before.values ++ [(2,false)]}
  have evaluated : phiBindings true [⟨0,1,2⟩] before.values = some [(2,false)] := by
    rw [values]
    rfl
  have merged : RawInstrument.merged true [⟨0,1,2⟩] before = some after := by
    rw [merged_actual,evaluated]
    rfl
  have represented : Represents before.values
      [.record wrapper ["empty","tag"],.record empty [],.bit]
      (.record wrapper [("empty",.record empty []),("tag",.bit false)])
      (.record wrapper [("empty",.record empty []),("tag",.bit 0)]) := by
    refine .record wrapper ["empty","tag"] [[.record empty []],[.bit]]
      [.record empty [],.bit false] [.record empty [],.bit 0] rfl ?_
    refine .cons _ _ _ _ _ _ (.record empty [] [] [] [] rfl .nil) ?_
    exact .cons _ _ _ _ _ _ (.bit 0 false (by rw [values]; rfl)) .nil
  have fresh : ∀ phi ∈ ([⟨0,1,2⟩] : List Observation.ClassicalPhi),
      lookup before.values phi.output = none := by
    intro phi member
    have same : phi = ⟨0,1,2⟩ := List.mem_singleton.mp member
    subst phi
    rw [values]
    rfl
  have unique : (([⟨0,1,2⟩] : List Observation.ClassicalPhi).map
      Observation.ClassicalPhi.output).Nodup := by decide
  exact ⟨after,merged,merged_transports before after true [⟨0,1,2⟩]
    represented complete_field_tree merged fresh unique⟩

private def single : FiniteCarrier.Origin := ⟨"demo","Single","enum Single { Only }"⟩
private def otherSingle : FiniteCarrier.Origin := ⟨"other","Single","enum Single { Only }"⟩

private theorem enum_origin {relation : Nat → Nat → Prop}
    {wanted actual : FiniteCarrier.Origin} {source target : List Nat}
    (moved : StorageTransport relation (.enumeration wanted source) (.enumeration actual target)) :
    wanted = actual := by
  cases moved
  rfl

/-- Zero physical coordinates do not erase a singleton enum's nominal origin. -/
theorem zero_width_nominal_origin :
    ¬ StorageTransport (fun _ _ => True) (.enumeration single []) (.enumeration otherSingle []) := by
  intro moved
  have identity := enum_origin moved
  have modules := congrArg FiniteCarrier.Origin.moduleName identity
  simp [single,otherSingle] at modules

private def mixed : FiniteCarrier.Origin :=
  ⟨"demo","Mixed","struct Mixed { empty: Empty, kept: Bit, changed: Bit }"⟩

/-- A kept ID need not appear among the new phi destinations. -/
theorem kept_identity_without_phi : KeptOrPhiEdge true [] 0 0 := .inl rfl

/-- Reuse does not permit replacing a leaf with an unrelated existing ID.
The actual output of this phi is 3, not 2. -/
theorem unrelated_kept_id_is_not_an_edge :
    ¬ KeptOrPhiEdge true [⟨1,2,3⟩] 1 2 := by
  simp [KeptOrPhiEdge,PhiEdge]

theorem unrelated_existing_bit_is_not_false :
    ¬ Represents [(0,true),(1,false),(2,true),(3,false)] [.bit] (.bit false) (.bit 2) := by
  intro represented
  cases represented with
  | bit id bit present => simp [lookup,List.find?] at present

/-- Empty field, unchanged ID, and fresh phi result retain their exact order. -/
theorem mixed_field_tree : StorageTransport (KeptOrPhiEdge true [⟨1,2,3⟩])
    (.record mixed [("empty",.record empty []),("kept",.bit 0),("changed",.bit 1)])
    (.record mixed [("empty",.record empty []),("kept",.bit 0),("changed",.bit 3)]) := by
  refine .record mixed _ _ (.cons "empty" _ _ _ _ (.record empty [] [] .nil) ?_)
  refine .cons "kept" _ _ _ _ (.bit 0 0 (.inl rfl)) ?_
  refine .cons "changed" _ _ [] [] (.bit 1 3 (.inr ?_)) .nil
  exact ⟨⟨1,2,3⟩,by simp,rfl,rfl⟩

/-- The actual mixed merge preserves the logical record for arbitrary hidden
history and quantum operator. There is no phi for the unchanged leaf at ID 0. -/
theorem actual_mixed_record_output (before : RawInstrument.History)
    (values : before.values = [(0,true),(1,false),(2,true)]) :
    ∃ after, RawInstrument.merged true [⟨1,2,3⟩] before = some after ∧
      Represents after.values
        [.record mixed ["empty","kept","changed"],.record empty [],.bit,.bit]
        (.record mixed [("empty",.record empty []),("kept",.bit true),("changed",.bit false)])
        (.record mixed [("empty",.record empty []),("kept",.bit 0),("changed",.bit 3)]) ∧
      after.hidden = before.hidden ∧ after.operator = before.operator := by
  let after : RawInstrument.History := {before with values := before.values ++ [(3,false)]}
  have evaluated : phiBindings true [⟨1,2,3⟩] before.values = some [(3,false)] := by
    rw [values]
    rfl
  have merged : RawInstrument.merged true [⟨1,2,3⟩] before = some after := by
    rw [merged_actual,evaluated]
    rfl
  have represented : Represents before.values
      [.record mixed ["empty","kept","changed"],.record empty [],.bit,.bit]
      (.record mixed [("empty",.record empty []),("kept",.bit true),("changed",.bit false)])
      (.record mixed [("empty",.record empty []),("kept",.bit 0),("changed",.bit 1)]) := by
    refine .record mixed ["empty","kept","changed"] [[.record empty []],[.bit],[.bit]]
      [.record empty [],.bit true,.bit false] [.record empty [],.bit 0,.bit 1] rfl ?_
    refine .cons _ _ _ _ _ _ (.record empty [] [] [] [] rfl .nil) ?_
    refine .cons _ _ _ _ _ _ (.bit 0 true (by rw [values]; rfl)) ?_
    exact .cons _ _ _ _ _ _ (.bit 1 false (by rw [values]; rfl)) .nil
  have fresh : ∀ phi ∈ ([⟨1,2,3⟩] : List Observation.ClassicalPhi),
      lookup before.values phi.output = none := by
    intro phi member
    have same : phi = ⟨1,2,3⟩ := List.mem_singleton.mp member
    subst phi
    rw [values]
    rfl
  have unique : (([⟨1,2,3⟩] : List Observation.ClassicalPhi).map
      Observation.ClassicalPhi.output).Nodup := by decide
  exact ⟨after,merged,merged_transports_kept before after true [⟨1,2,3⟩]
    represented mixed_field_tree merged fresh unique⟩

end Qleisli.Semantics.OrdinaryValue.PhiExamples
