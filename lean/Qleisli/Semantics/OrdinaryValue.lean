import QleisliKernel.Semantics.OrdinaryValue
import Qleisli.Semantics.RawInstrument

/-! Ordinary-value lemmas about the existing Raw event semantics.
The lemmas connect lookup, classical actions and simultaneous phi reads to
actual Raw definitions. Preservation of existing represented values does not
establish a new phi output tree, source-member authorization or typed replay.
No new execution engine, acceptance predicate or source-preservation claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue
open RawInstrument

theorem lookup_actual (values : Valuation) (id : Nat) :
    lookup values id = RawInstrument.value values id := rfl

/-- The exact phi operands are read from the incoming history together. No
earlier output in this list is available as an operand for a later phi. -/
def phiBindings (choice : Bool) (phis : List Observation.ClassicalPhi)
    (values : Valuation) : Option Valuation :=
  phis.mapM fun phi => do
    pure (phi.output,← RawInstrument.value values (if choice then phi.thenId else phi.elseId))

theorem merged_actual (choice : Bool) (phis : List Observation.ClassicalPhi) (history : History) :
    RawInstrument.merged choice phis history =
      (phiBindings choice phis history.values).map
        (fun added => {history with values := history.values ++ added}) := by
  change (phiBindings choice phis history.values).bind
      (fun added => some {history with values := history.values ++ added}) =
    (phiBindings choice phis history.values).map
      (fun added => {history with values := history.values ++ added})
  cases phiBindings choice phis history.values <;> rfl

/-- An actual classical event preserves every previously represented ordinary
value, creates its actual fresh Bit, and leaves the complete quantum operator
and hidden history unchanged. No product/separability premise is imposed. -/
theorem classical_preserves {basis logical storage} (initial : History)
    (dependencies : List QleisliKernel.Semantics.Finite.Dependency)
    (expr : Observation.Expr) (output : Nat) (result : Bool)
    (represented : Represents initial.values basis logical storage)
    (evaluated : RawInstrument.expression initial.values expr = some result)
    (fresh : lookup initial.values output = none) :
    let next := {initial with values := initial.values ++ [(output,result)]}
    Action dependencies (.classical expr output) initial [next] ∧
      Represents next.values basis logical storage ∧
      Represents next.values [.bit] (.bit result) (.bit output) ∧
      next.hidden = initial.hidden ∧ next.operator = initial.operator := by
  dsimp only
  exact ⟨.classical expr output initial result evaluated,
    represented.extends (append_extends _ _),
    .bit output result (lookup_append_fresh result fresh),rfl,rfl⟩

/-- This lemma retains old values across the actual simultaneous merge. It
does not yet prove that a newly described output tree selects matching children;
that exact phi-to-tree correspondence is a separate replay obligation. -/
theorem merged_preserves {basis logical storage} (before after : History)
    (choice : Bool) (phis : List Observation.ClassicalPhi)
    (represented : Represents before.values basis logical storage)
    (merged : RawInstrument.merged choice phis before = some after) :
    Represents after.values basis logical storage ∧
      after.hidden = before.hidden ∧ after.operator = before.operator := by
  rw [merged_actual] at merged
  cases bindings : phiBindings choice phis before.values with
  | none => simp [bindings] at merged
  | some added =>
    simp only [bindings,Option.map_some,Option.some.injEq] at merged
    subst after
    exact ⟨represented.extends (append_extends _ _),rfl,rfl⟩

/-- Literal Raw decoding of a classical constant does not consume or duplicate
any quantum owner, including zero-width ports in the supplied complete frame. -/
theorem read_constant_frame (fuel : Nat) (frame : RawTrace.Interface) (bit : Bool) (id : Nat) :
    Observation.readOps (fuel + 1) frame [.constant bit id] =
      some (frame,[.classical (.constant bit) id]) := rfl

end Qleisli.Semantics.OrdinaryValue
