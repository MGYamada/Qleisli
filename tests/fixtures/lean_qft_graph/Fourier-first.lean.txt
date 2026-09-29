import Qleisli.Qft
import QleisliKernel.QftGraph

/-! Fourier semantics of the actual accepted typed shared circuit projection.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.QftGraph
open QleisliKernel QleisliKernel.Interference QleisliKernel.PathSum
open Qleisli.Interference Qleisli.Qft

/-- Literal operational graph coefficient: sum all H paths at the final output.
Only accepted QFT graphs have exactly `width` H choices. This proof-only finite
sum is never evaluated by the executable checker. -/
noncomputable def coefficient (width : Nat) (actual : QleisliKernel.QftGraph.Action)
    (input output : Fin width → Bool) : ℂ :=
  ∑ choices : Fin width → Bool,
    let result := actual (finiteBits choices)
      (realize width (initial width) (finiteBits input) (finiteBits choices))
    if (fun i : Fin width => result.bits i) = output then pathWeight result else 0

/-- Acceptance determines the whole typed boundary and literal graph action;
the mathematical coefficient below is computed from that action, not a receipt. -/
theorem check_fourier (definitions : List QleisliKernel.QftGraph.Definition)
    (entry width : Nat) (receipt : QleisliKernel.QftGraph.Receipt)
    (accepted : QleisliKernel.QftGraph.check definitions entry width = some receipt)
    (actual : QleisliKernel.QftGraph.Action)
    (meaning : QleisliKernel.QftGraph.denote definitions entry = some actual)
    (input output : Fin width → Bool) :
    coefficient width actual input output =
      Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) /
      (Real.sqrt ((2 : ℝ) ^ width) : ℂ) := by
  obtain ⟨_, _, matched⟩ := QleisliKernel.QftGraph.check_sound
    definitions entry width receipt accepted
  have bound := QleisliKernel.QftGraph.check_action definitions entry width receipt accepted
  rw [meaning] at bound
  cases Option.some.inj bound
  have endpoints (choices : Fin width → Bool) :
      (fun i : Fin width =>
        (QleisliKernel.QftGraph.permute (QleisliKernel.Qft.finalAxes width)
          (runFrom receipt.summary.gates (finiteBits choices)
            (realize width (initial width) (finiteBits input) (finiteBits choices)))).bits i) =
        choices := by
    funext i
    simp only [QleisliKernel.QftGraph.permute, Function.comp_apply,
      QleisliKernel.QftGraph.reversal_index width i i.isLt]
    rw [QleisliKernel.Qft.matched_output width i i.isLt receipt.summary.gates
      (receipt.summary.axes.getD []) matched]
    exact finiteBits_inside choices i
  simp only [coefficient, endpoints, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change pathWeight (runFrom receipt.summary.gates (finiteBits output)
    (realize width (initial width) (finiteBits input) (finiteBits output))) = _
  rw [matched_weight width receipt.summary.gates (receipt.summary.axes.getD []) matched,
    halfRoot_power]
  ring

/-- Arbitrary reference amplitudes survive the accepted graph equation. -/
theorem check_reference (definitions : List QleisliKernel.QftGraph.Definition)
    (entry width : Nat) (receipt : QleisliKernel.QftGraph.Receipt)
    (accepted : QleisliKernel.QftGraph.check definitions entry width = some receipt)
    (actual : QleisliKernel.QftGraph.Action)
    (meaning : QleisliKernel.QftGraph.denote definitions entry = some actual)
    {R : Type} (joint : (Fin width → Bool) → R → ℂ) (reference : R)
    (output : Fin width → Bool) :
    (∑ input, coefficient width actual input output * joint input reference) =
      ∑ input, (Complex.exp (2 * Real.pi * Complex.I * value width (finiteBits input) *
        value width (finiteBits output) / (2 : ℂ) ^ width) /
        (Real.sqrt ((2 : ℝ) ^ width) : ℂ)) * joint input reference := by
  apply Finset.sum_congr rfl
  intro input _
  rw [check_fourier definitions entry width receipt accepted actual meaning input output]

end Qleisli.QftGraph
