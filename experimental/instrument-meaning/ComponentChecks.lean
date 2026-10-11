import QleisliKernel.Raw.InstrumentEquality

/-! Small checked regressions of the unwired exact coefficient component.
No public signature, source or accepted-handle gate is asserted here.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Experiments.InstrumentComponentChecks
open QleisliKernel.Semantics.Exact QleisliKernel.Finite
open QleisliKernel.Raw.InstrumentEquality

private def one : History := ⟨[],⟨1,1,[Scalar.one]⟩⟩
private def negative : History := ⟨[],⟨1,1,[⟨.integer (-1),.integer 0,.integer 0,.integer 0⟩]⟩⟩
private def halfRoot : History := ⟨[],⟨1,1,[⟨.integer 0,⟨1,1⟩,.integer 0,.integer 0⟩]⟩⟩
private def impossible : History := ⟨[true],⟨1,1,[Scalar.zero]⟩⟩
private def run (rows cols results : Nat) (actual expected : List History) :=
  (QleisliKernel.Raw.InstrumentEquality.compare rows cols results actual expected).run 10000
private def agrees (actual expected : Except Error Unit) : Bool :=
  match actual, expected with
  | .ok _, .ok _ => true
  | .error a, .error b => a == b
  | _, _ => false

example : agrees (run 1 1 0 [one] [one]).1 (.ok ()) = true := by decide
example : agrees (run 1 1 0 [one] [negative]).1 (.ok ()) = true := by decide
example : agrees (run 1 1 0 [one] [halfRoot,halfRoot]).1 (.ok ()) = true := by decide
example : agrees (run 1 1 1 [{one with outcome := [false]}]
    [{one with outcome := [false]},impossible]).1 (.ok ()) = true := by decide
example : agrees (run 1 1 0 [] [one]).1 (.error .invalid) = true := by decide
example : agrees (run 1 1 0 [one] []).1 (.error .invalid) = true := by decide
example : agrees (run 1 1 1 [one] [one]).1 (.error .invalid) = true := by decide
example : agrees (run 2 1 0 [one] [one]).1 (.error .invalid) = true := by decide
example : agrees (run 1 1 0 [{one with operator := ⟨1,1,[]⟩}] [one]).1 (.error .invalid) = true := by decide
example : agrees (run 1 1 0 [{one with operator := ⟨1,1,[⟨⟨0,1⟩,.integer 0,.integer 0,.integer 0⟩]⟩}]
    [one]).1 (.error .invalid) = true := by decide
example : agrees (run 0 1 0 [one] [one]).1 (.error .limit) = true := by decide
example : agrees ((QleisliKernel.Raw.InstrumentEquality.compare 1 1 0 [one] [one]).run 0).1
    (.error (.arithmetic .workLimit)) = true := by decide

end Qleisli.Experiments.InstrumentComponentChecks
