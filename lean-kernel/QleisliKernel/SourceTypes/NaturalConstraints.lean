import QleisliKernel.SourceTypes.NaturalAffine

/-! Exact bounded elimination of integer affine inequalities. Every retained
row carries preservation from the original rows, including after normalization.
A successful contradiction returns its proof, never a caller success receipt.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalConstraints
open Semantics.SourceAffine NaturalAffine

structure Certified (source : List Form) where
  form : Form
  bound : ∀ values, Holds source values → form.evaluate values ≤ 0

abbrev NoValues (source : List Form) := ∀ values, ¬ Holds source values

structure Unsatisfiable (source : List Form) : Type where
  witness : NoValues source

private def gcdWork : Nat → Nat → Nat → WorkM Nat :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse a b => do
    Finite.exactWork (Exact.charge 1)
    if b == 0 then return a
    recurse b (a % b))

private def normalize {source : List Form} (input : Certified source) : WorkM (Certified source) := do
  valid input.form
  let divisor ← input.form.coefficients.foldlM
    (fun prior coefficient => gcdWork 256 prior coefficient.natAbs) input.form.constant.natAbs
  if small : divisor ≤ 1 then return input
  else
    let factor : Int := divisor
    let _ ← checked factor
    let result : Form := ⟨input.form.constant / factor,input.form.coefficients.map (· / factor)⟩
    valid result
    if same : result.scale factor = input.form then
      return ⟨result,by
        intro values original
        have bound := input.bound values original
        have scaled : factor * result.evaluate values = input.form.evaluate values := by
          rw [← Form.evaluate_scale,same]
        have positive : 0 < factor := by omega
        apply (Int.mul_le_mul_left positive).mp
        simpa only [Int.mul_zero,scaled] using bound⟩
    else throw .request

private def combination {source : List Form} (index : Nat)
    (positive negative : Certified source) : WorkM (Certified source) := do
  let p := positive.form.coefficients[index]?.getD 0
  let n := negative.form.coefficients[index]?.getD 0
  if signs : 0 < p ∧ n < 0 then
    let _ ← checked (-n)
    let _ ← checked p
    let first := positive.form.scale (-n)
    let second := negative.form.scale p
    valid first
    valid second
    if same : first.coefficients.length = second.coefficients.length then
      let result := first.add second
      valid result
      normalize ⟨result,by
        intro values original
        rw [Form.evaluate_add _ _ same,Form.evaluate_scale,Form.evaluate_scale]
        exact Int.add_nonpos
          (Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (positive.bound values original))
          (Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (negative.bound values original))⟩
    else throw .request
  else throw .request

private def insert {source : List Form} (rows : List (Certified source))
    (row : Certified source) : WorkM (List (Certified source)) := do
  Finite.exactWork (Exact.charge (rows.length*(row.form.coefficients.length+1)+1))
  if rows.any (fun prior => prior.form == row.form) then return rows
  Finite.guard (rows.length < 4096) .limit
  return row :: rows

private def eliminate {source : List Form} (index : Nat) (rows : List (Certified source))
    (pairs : Nat) : WorkM (List (Certified source) × Nat) := do
  Finite.exactWork (Exact.charge (rows.length*3+1))
  let positive := rows.filter (fun row => row.form.coefficients[index]?.getD 0 > 0)
  let negative := rows.filter (fun row => row.form.coefficients[index]?.getD 0 < 0)
  let zero := rows.filter (fun row => row.form.coefficients[index]?.getD 0 == 0)
  let retained ← zero.foldlM (fun prior row => do insert prior (← normalize row)) []
  positive.foldlM (fun (retained,pairs) a =>
    negative.foldlM (fun (retained,pairs) b => do
      Finite.guard (pairs < 50000 && retained.length < 4096) .limit
      let result ← combination index a b
      return (← insert retained result,pairs+1)) (retained,pairs)) (retained,pairs)

private def contradiction {source : List Form} (rows : List (Certified source)) : Option (Unsatisfiable source) :=
  rows.foldr (fun row prior =>
    if constant : isConstant row.form = true then
      if positive : 0 < row.form.constant then
        some ⟨fun values original => by
          have bound := row.bound values original
          rw [isConstant_meaning row.form constant values] at bound
          omega⟩
      else prior
    else prior) none

private def choose {source : List Form} (dimension : Nat) (rows : List (Certified source)) :
    WorkM (Option Nat) := do
  Finite.exactWork (Exact.charge (dimension*(rows.length*3+1)+1))
  let variables := (List.range dimension).filter (fun i =>
    rows.any (fun row => row.form.coefficients[i]?.getD 0 != 0))
  let best := variables.foldl (fun best i =>
    let p := (rows.filter (fun row => row.form.coefficients[i]?.getD 0 > 0)).length
    let n := (rows.filter (fun row => row.form.coefficients[i]?.getD 0 < 0)).length
    match best with
    | none => some (i,p*n)
    | some (previous,score) => if p*n < score then some (i,p*n) else some (previous,score)) none
  return best.map Prod.fst

private def loop {source : List Form} (dimension : Nat) :
    Nat → List (Certified source) → Nat → WorkM (Option (Unsatisfiable source)) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse rows pairs => do
    Finite.exactWork (Exact.charge (rows.length+1))
    if let some proof := contradiction rows then return some proof
    let some index ← choose dimension rows | return none
    let (next,pairs) ← eliminate index rows pairs
    recurse next pairs)

/-- Same bounded rational-relaxation rule: a contradiction proves impossibility;
no contradiction is not a proof of an integer witness. Capacity failures reject. -/
def check (source : List Form) : WorkM (Option (Unsatisfiable source)) := do
  Finite.guard (source.length ≤ 4096) .limit
  let dimension := source.head?.map (·.coefficients.length) |>.getD 0
  Finite.guard (dimension ≤ 32) .limit
  let rows ← source.attach.mapM fun row => do
    valid row.val
    Finite.guard (row.val.coefficients.length == dimension) .request
    return (⟨row.val,fun _values original => original row.val row.property⟩ : Certified source)
  loop dimension (dimension+1) rows 0

end QleisliKernel.SourceTypes.NaturalConstraints
