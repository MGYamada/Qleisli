import QleisliKernel.Semantics.OrdinaryValue

/-! Ordinary-value examples checked by the library build and compiled audit.
These cover finite values and representation relations, not program acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.OrdinaryValue.Examples
open FiniteCarrier

private def tri : Origin := ⟨"demo","Tri","enum Tri { A, B, C }"⟩
private def other : Origin := ⟨"other","Tri","enum Tri { A, B, C }"⟩
private def single : Origin := ⟨"demo","Single","enum Single { Only }"⟩
private def empty : Origin := ⟨"demo","Empty","struct Empty {}"⟩
private def wrapper : Origin := ⟨"demo","Wrapper","struct Wrapper { empty: Empty, tag: Tri }"⟩
private def variants : List String := ["A","B","C"]

/-- A three-case enum occupies two coordinates, but has only three values. -/
theorem tri_two : Represents [(10,false),(11,true)] [.enumeration tri variants]
    (.enumeration tri 2) (.enumeration tri [10,11]) := by
  refine .enumeration tri variants 2 [10,11] [false,true] (by decide) (by decide) ?_ rfl
  exact .cons 10 false [11] [true] rfl (.cons 11 true [] [] rfl .nil)

theorem tri_not_three : ¬ ValueOf [.enumeration tri variants] (.enumeration tri 3) := by
  intro typed
  have outside := typed.enum_range
  simp [variants] at outside

/-- Equal cardinality, width, spelling and bytes do not erase module identity. -/
theorem no_same_width_retype : ¬ ValueOf [.enumeration tri variants] (.enumeration other 2) := by
  intro typed
  have same := typed.enum_identity
  have modules := congrArg Origin.moduleName same
  simp [tri,other] at modules

theorem singleton_keeps_node : Represents [] [.enumeration single ["Only"]]
    (.enumeration single 0) (.enumeration single []) :=
  .enumeration single ["Only"] 0 [] [] (by decide) (by decide) .nil rfl

theorem empty_record_keeps_node : Represents [] [.record empty []]
    (.record empty []) (.record empty []) :=
  .record empty [] [] [] [] rfl .nil

theorem unit_is_not_bits_zero : ¬ Represents [] [.unit] (.bits []) (.bits []) := by
  intro represented
  cases represented

theorem empty_record_is_not_unit : ¬ Represents [] [.record empty []] .unit .unit := by
  have unit_type (basis : Basis) (evidence : Represents [] basis .unit .unit) :
      basis = [.unit] := by
    cases evidence
    rfl
  intro represented
  have impossible := unit_type _ represented
  cases impossible

theorem copy_keeps_zero_nodes : Represents [] [.pair,.record empty [],.record empty []]
    (.pair (.record empty []) (.record empty []))
    (.pair (.record empty []) (.record empty [])) := empty_record_keeps_node.copy

/-- Declared order retains a zero-width field before the enum tag. -/
theorem record_in_declaration_order : Represents [(10,false),(11,true)]
    [.record wrapper ["empty","tag"],.record empty [],.enumeration tri variants]
    (.record wrapper [("empty",.record empty []),("tag",.enumeration tri 2)])
    (.record wrapper [("empty",.record empty []),("tag",.enumeration tri [10,11])]) := by
  refine .record wrapper ["empty","tag"] [[.record empty []],[.enumeration tri variants]]
    [.record empty [],.enumeration tri 2] [.record empty [],.enumeration tri [10,11]] rfl ?_
  exact .cons _ _ _ _ _ _ (.record empty [] [] [] [] rfl .nil)
    (.cons _ _ _ _ _ _ tri_two .nil)

theorem no_reordered_fields (tail : Basis) : ¬ ValueOf
    (.record wrapper ["empty","tag"] :: tail)
    (.record wrapper [("tag",.enumeration tri 2),("empty",.record empty [])]) := by
  intro typed
  have names := typed.record_names
  simp at names

theorem no_omitted_zero_field (tail : Basis) : ¬ ValueOf
    (.record wrapper ["empty","tag"] :: tail)
    (.record wrapper [("tag",.enumeration tri 2)]) := by
  intro typed
  have names := typed.record_names
  simp at names

/-- Physical width alone cannot justify an ordinal outside the logical range. -/
theorem bad_tag_cannot_represent :
    ¬ Represents [(10,true),(11,true)] [.enumeration tri variants]
      (.enumeration tri 3) (.enumeration tri [10,11]) := by
  intro represented
  exact tri_not_three represented.typed

/-- A producer cannot relabel the actual out-of-range bits as a valid ordinal. -/
theorem invalid_physical_tag_is_not_two :
    ¬ Represents [(10,true),(11,true)] [.enumeration tri variants]
      (.enumeration tri 2) (.enumeration tri [10,11]) := by
  intro represented
  cases represented with
  | enumeration origin variants ordinal ids bits range width read encoded =>
    have actual : Reads [(10,true),(11,true)] [10,11] [true,true] :=
      .cons 10 true [11] [true] rfl (.cons 11 true [] [] rfl .nil)
    have same := read.unique actual
    rw [same] at encoded
    simp [littleEndian] at encoded

end QleisliKernel.Semantics.OrdinaryValue.Examples
