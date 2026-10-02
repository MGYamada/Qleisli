import QleisliKernel.Semantics.Observation

/-! Bounded equality of complete original observing bodies. Recursive derived
equality is avoided so all compiled helpers remain ordinary total definitions.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.ObservationBinding
open Semantics.Observation

def lists {α : Type} (same : α → α → Bool) (xs ys : List α) : Bool :=
  xs.length == ys.length && (xs.zip ys).all (fun (x,y) => same x y)

theorem lists_sound {α : Type} (same : α → α → Bool)
    (sound : ∀ x y, same x y = true → x = y) (xs ys : List α)
    (ok : lists same xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [lists]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lists] at ok
    | cons y ys =>
      simp only [lists,List.length_cons,List.zip_cons_cons,List.all_cons,
        Bool.and_eq_true,beq_iff_eq,Nat.succ.injEq] at ok
      have hx := sound _ _ ok.2.1
      have hs := ih ys (by
        simpa only [lists,Bool.and_eq_true,beq_iff_eq] using And.intro ok.1 ok.2.2)
      rw [hx,hs]

def operation (fuel : Nat) : Op → Op → Bool :=
  Nat.rec (fun _ _ => false) (fun _ recurse a b => match a,b with
    | .pure a,.pure b => a == b
    | .measure a c,.measure b d | .not a c,.not b d => a == b && c == d
    | .reset a c e,.reset b d f | .xor a c e,.xor b d f | .and a c e,.and b d f =>
      a == b && c == d && e == f
    | .discard a,.discard b => a == b
    | .constant a c,.constant b d => a == b && c == d
    | .branch a l r q c,.branch b l' r' q' c' =>
      a == b && lists recurse l l' && lists recurse r r' && q == q' && c == c'
    | _,_ => false) fuel

theorem operation_sound (fuel : Nat) (a b : Op) (ok : operation fuel a b = true) : a = b := by
  induction fuel generalizing a b with
  | zero => cases ok
  | succ fuel ih =>
    cases a <;> cases b <;>
      simp only [operation,Bool.and_eq_true,beq_iff_eq] at ok
    all_goals try contradiction
    all_goals try {rcases ok with ⟨⟨h₁,h₂⟩,h₃⟩; subst_vars; rfl}
    all_goals try {rcases ok with ⟨h₁,h₂⟩; subst_vars; rfl}
    all_goals try {subst_vars; rfl}
    rcases ok with ⟨⟨⟨⟨condition,left⟩,right⟩,quantum⟩,classical⟩
    have hl := lists_sound _ ih _ _ left
    have hr := lists_sound _ ih _ _ right
    subst_vars
    rfl

def program (a b : Program) : Bool :=
  a.inputs == b.inputs && a.classicalInputs == b.classicalInputs &&
    lists (operation 65) a.operations b.operations && a.outputs == b.outputs &&
    a.classicalOutputs == b.classicalOutputs && a.effect == b.effect

theorem program_sound (a b : Program) (ok : program a b = true) : a = b := by
  simp only [program,Bool.and_eq_true,beq_iff_eq] at ok
  rcases ok with ⟨⟨⟨⟨⟨inputs,ci⟩,ops⟩,outputs⟩,co⟩,effect⟩
  have same := lists_sound _ (operation_sound 65) _ _ ops
  cases a; cases b; simp_all

end QleisliKernel.ObservationBinding
