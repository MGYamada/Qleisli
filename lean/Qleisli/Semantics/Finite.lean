import QleisliKernel.Semantics.Finite
import Qleisli.Semantics.Exact

/-! Independent literal finite-circuit reference. Gate amplitudes, ordered axes
and encoded composition are mathematical definitions, not acceptance summaries.
No arithmetic, checker, cache validity or transport module is imported.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open Qleisli.Semantics.Exact

noncomputable def halfRoot : ℂ := (Real.sqrt 2 : ℂ) / 2
noncomputable def phase (k : Nat) : ℂ :=
  match k % 8 with
  | 0 => 1 | 1 => halfRoot + Complex.I * halfRoot
  | 2 => Complex.I | 3 => -halfRoot + Complex.I * halfRoot
  | 4 => -1 | 5 => -halfRoot - Complex.I * halfRoot
  | 6 => -Complex.I | _ => halfRoot - Complex.I * halfRoot

/-- Unbounded conjugation of the data representation, with no capacity rule. -/
def rawStar (value : Scalar) : Scalar :=
  ⟨value.a,value.b,⟨-value.c.numerator,value.c.exponent⟩,
    ⟨-value.d.numerator,value.d.exponent⟩⟩

/-- Literal local action, including inactive controls and scalar Unit phases. -/
noncomputable def contributions (dependencies : List Dependency) (step : Step)
    (label : Nat) (value : Scalar) : Option (List (Nat × ℂ)) := do
  if value == Scalar.zero then return []
  let amplitude := scalar value
  if !enabled step.controls label then return [(label,amplitude)]
  match step.action with
  | .hadamard target =>
    let low := label - bit label target * 2^target
    let high := low + 2^target
    return [(low,amplitude * halfRoot),
      (high,if label == high then -(amplitude * halfRoot) else amplitude * halfRoot)]
  | .monomial axes permutation phases =>
    let input := gather label axes
    let output ← permutation[input]?
    let exponent ← phases[input]?
    return [(scatter label axes output,amplitude * phase exponent)]
  | .contract axes index adjoint =>
    let dependency ← dependencies[index]?
    let input := gather label axes
    (List.range dependency.meaning.rows).foldlM (fun terms output =>
      let coefficient := if adjoint then star (entry dependency.meaning input output)
        else entry dependency.meaning output input
      -- Omitting an exact zero does not change the literal sum. The reference
      -- uses data equality only and assumes no successful acceptance predicate.
      let raw := if adjoint then rawStar (dependency.meaning.entry input output)
        else dependency.meaning.entry output input
      pure (if raw == Scalar.zero then terms
        else terms ++ [(scatter label axes output,amplitude * coefficient)])) []

/-- A reference for original finite vectors is also useful before proving linear
extension; this uses unbounded exact complex arithmetic and has no work policy. -/
noncomputable def addAt (values : List ℂ) (term : Nat × ℂ) : List ℂ :=
  values.set term.1 (values[term.1]?.getD 0 + term.2)

/-- Literal complex evaluation of one step on an original data vector. The data
representation only determines omitted zero terms; arithmetic is unbounded. -/
noncomputable def applyStep (dependencies : List Dependency) (step : Step)
    (values : List Scalar) : Option (List ℂ) :=
  values.zipIdx.foldlM (fun next (value,label) => do
    let terms ← contributions dependencies step label value
    pure (terms.foldl addAt next)) (List.replicate values.length 0)

/-- A literal execution trace exposes each intermediate vector and its full
complex action. It assumes no checker, producer receipt, cache or work policy. -/
inductive Trace (dependencies : List Dependency) : List Step → List Scalar → List Scalar → Prop
  | nil (values) : Trace dependencies [] values values
  | cons (step steps values next result)
      (localAction : applyStep dependencies step values = some (next.map scalar))
      (rest : Trace dependencies steps next result) :
      Trace dependencies (step :: steps) values result

/-- Coefficients of the encoded operator equation, independently stated. -/
noncomputable def Encoded (actual : Matrix) (contract : Contract) : Prop :=
  actual.cols = contract.input.map.rows ∧
  contract.output.map.cols = contract.logical.rows ∧
  actual.rows = contract.output.map.rows ∧ contract.input.map.cols = contract.logical.cols ∧
  ∀ row col, row < actual.rows → col < contract.logical.cols →
    ((List.range actual.cols).map (fun k => entry actual row k * entry contract.input.map k col)).sum =
    ((List.range contract.output.map.cols).map
      (fun k => entry contract.output.map row k * entry contract.logical k col)).sum

end Qleisli.Semantics.Finite
