import QleisliKernel.Semantics.SourceNaturalBounds
import QleisliKernel.SourceTypes.NaturalHelpers
import QleisliKernel.SourceTypes.NaturalNormalize

/-! Closed ordinary Nat computations with original, proof-carrying alias lookup.
The original helper checker and exact mathematical evaluator remain shared.
Original token, lexical-scope and caller-actual binding remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalClosed
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite
open QleisliKernel.Semantics.SourceNatural QleisliKernel.Semantics.SourceAffine

abbrev NameReader (names : Names) (calls : Calls) := ∀ fuel path,
  WorkM (NaturalNormalize.Result (fun _ => names) calls (fun _ => True) (fuel+1) (.name path))

private def context : NaturalPredicates.Context (fun _ => True) :=
  ⟨[[]],by intro values; simp [Satisfies,Holds]⟩

structure NodeValue (names : Names) (calls : Calls) (expression : Expr) where
  value : Nat
  bounded : value ≤ 4294967295
  computed : evaluate 128 names calls expression = some value

private def nodeValue (names : Names) (entries : List NaturalHelpers.Entry)
    (bindings : List (Path × NaturalCatalog.Key))
    (readName : NameReader names (NaturalHelpers.interpretation entries bindings)) (expression : Expr) :
    WorkM (NodeValue names (NaturalHelpers.interpretation entries bindings) expression) := do
  let calls := NaturalHelpers.interpretation entries bindings
  let normalized ← NaturalNormalize.normalize 0 context
    ⟨readName,NaturalHelpers.readCall 0 (fun _ => names) entries bindings context⟩ 128 expression
  if shape : normalized.form.coefficients = [] then
    if bounds : 0 ≤ normalized.form.constant ∧ normalized.form.constant ≤ 4294967295 then
      let value := normalized.form.constant.toNat
      return ⟨value,by omega,by
        obtain ⟨n,computed,same⟩ := normalized.correct (fun _ => 0) True.intro
        have numeric : normalized.form.constant = (n : Int) := by
          simpa only [Form.evaluate,shape,dot_nil,Int.add_zero] using same
        have equal : value = n := by omega
        rw [equal]
        exact computed⟩
    else throw .limit
  else throw .request

private def allChildren {names calls}
    (read : ∀ expression,WorkM (NaturalPredicates.Established (Semantics.SourceNatural.Bounds.AllU32 names calls expression))) :
    Nat → (expressions : List Expr) →
    WorkM (NaturalPredicates.Established (∀ expression ∈ expressions,Semantics.SourceNatural.Bounds.AllU32 names calls expression)) :=
  Nat.rec (fun expressions => match expressions with
    | [] => pure ⟨by intro _ member; cases member⟩
    | _ :: _ => throw .limit)
    (fun _ next expressions => do
      match expressions with
      | [] => return ⟨by intro _ member; cases member⟩
      | expression :: remaining =>
        let first ← read expression
        let rest ← next remaining
        return ⟨by
          intro other member
          rcases List.mem_cons.mp member with same | member
          · subst other; exact first.proof
          · exact rest.proof other member⟩)

structure Checked (names : Names) (calls : Calls) (expression : Expr) extends NodeValue names calls expression where
  allU32 : Semantics.SourceNatural.Bounds.AllU32 names calls expression

private def checkNodes (names : Names) (entries : List NaturalHelpers.Entry)
    (bindings : List (Path × NaturalCatalog.Key))
    (readName : NameReader names (NaturalHelpers.interpretation entries bindings)) :
    Nat → (expression : Expr) → WorkM (Checked names (NaturalHelpers.interpretation entries bindings) expression) :=
  Nat.rec (fun _ => throw .limit) (fun _ next expression => do
    exactWork (Exact.charge (1 + (Semantics.SourceNatural.Bounds.children expression).length))
    let operands ← allChildren (fun child => do
      let result ← next child
      pure ⟨result.allU32⟩) ((Semantics.SourceNatural.Bounds.children expression).length+1) (Semantics.SourceNatural.Bounds.children expression)
    let result ← nodeValue names entries bindings readName expression
    return ⟨result,.node expression result.value (evaluate_value _ _ _ _ _ result.computed)
      result.bounded operands.proof⟩)

def read (names : Names) (entries : List NaturalHelpers.Entry)
    (bindings : List (Path × NaturalCatalog.Key))
    (readName : NameReader names (NaturalHelpers.interpretation entries bindings)) (expression : Expr) :
    WorkM (Checked names (NaturalHelpers.interpretation entries bindings) expression) :=
  checkNodes names entries bindings readName 129 expression

def empty : Names := fun _ => none

def emptyReader (calls : Calls) : NameReader empty calls := fun _ _ => throw .request

/-- This mathematical lookup executes the actual original initializer under
its earlier lexical environment. It is not a stored integer or later scope. -/
def extend (previous : Names) (calls : Calls) (name : String) (initializer : Expr) : Names :=
  fun path => if path = [name] then evaluate 128 previous calls initializer else previous path

end QleisliKernel.SourceTypes.NaturalClosed
