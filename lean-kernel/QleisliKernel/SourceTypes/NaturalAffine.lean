import QleisliKernel.Semantics.SourceAffine
import QleisliKernel.Finite

/-! Bounded exact affine operations over an original formal-parameter frame.
All slots/constants use checked signed i128 intermediates. This module grants
no original source/helper binding or successful implication by itself.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalAffine
open Semantics.SourceAffine

abbrev Error := Finite.Error
abbrev WorkM := Finite.WorkM

/-- Retain proof of this actual computation; no supplied success receipt is
decoded or trusted. The proof is erased and the work state is unchanged. -/
def witness {α : Type} (action : WorkM α) :
    WorkM {value : α // ∃ work left, action.run work = (.ok value,left)} := fun work =>
  match success : action.run work with
  | (.error error,left) => (.error error,left)
  | (.ok value,left) => (.ok ⟨value,work,left,success⟩,left)

def fits (value : Int) : Bool :=
  -170141183460469231731687303715884105728 ≤ value &&
    value ≤ 170141183460469231731687303715884105727

def checked (value : Int) : WorkM Int := do
  Finite.exactWork (Exact.charge 1)
  Finite.guard (fits value) .limit
  return value

def valid (a : Form) : WorkM Unit := do
  Finite.guard (a.coefficients.length ≤ 32) .limit
  let _ ← checked a.constant
  let _ ← a.coefficients.mapM checked
  pure ()

def constant (variables : Nat) (value : Int) : WorkM Form := do
  Finite.guard (variables ≤ 32) .limit
  let value ← checked value
  Finite.exactWork (Exact.charge (variables+1))
  return ⟨value,List.replicate variables 0⟩

def parameter (variables position : Nat) : WorkM Form := do
  Finite.guard (variables ≤ 32 && position < variables) .limit
  Finite.exactWork (Exact.charge (variables+1))
  return coordinate variables position

def scale (factor : Int) (a : Form) : WorkM Form := do
  valid a
  let _ ← checked factor
  let result := a.scale factor
  valid result
  return result

def add (a b : Form) : WorkM Form := do
  valid a
  valid b
  Finite.guard (a.coefficients.length == b.coefficients.length) .request
  let result := a.add b
  valid result
  return result

/-- Match the existing checked negation-then-addition order, even when an
unbounded mathematical subtraction could cancel an overflowing negation. -/
def sub (a b : Form) : WorkM Form := do
  add a (← scale (-1) b)

def isConstant (a : Form) : Bool := a.coefficients.all (· == 0)

def multiply (a b : Form) : WorkM Form := do
  valid a
  valid b
  Finite.guard (a.coefficients.length == b.coefficients.length) .request
  if isConstant a then scale a.constant b
  else if isConstant b then scale b.constant a
  else throw .request

theorem checked_value (value result : Int) (work left : Nat)
    (ok : (checked value).run work = (.ok result,left)) : result = value ∧ fits value = true := by
  obtain ⟨_,a,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,b,guarded,h⟩ := Finite.bind_success _ _ _ _ _ h
  exact ⟨(Finite.pure_success _ _ _ _ h).1,(Finite.guard_success _ _ _ _ guarded).1⟩

theorem constant_value (variables : Nat) (value : Int) (result : Form) (work left : Nat)
    (ok : (constant variables value).run work = (.ok result,left)) :
    result = ⟨value,List.replicate variables 0⟩ := by
  obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨actual,w₂,checked,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  have same := (checked_value _ _ _ _ checked).1
  simpa only [same] using (Finite.pure_success _ _ _ _ h).1

theorem constant_meaning (variables : Nat) (value : Int) (result : Form) (work left : Nat)
    (ok : (constant variables value).run work = (.ok result,left)) (values : Valuation) :
    result.evaluate values = value := by
  rw [constant_value _ _ _ _ _ ok]
  have zero : (List.replicate variables (0 : Int)).all (· == 0) = true := by simp
  simp only [Form.evaluate,dot_zero _ zero,Int.add_zero]

theorem parameter_value (variables position : Nat) (result : Form) (work left : Nat)
    (ok : (parameter variables position).run work = (.ok result,left)) :
    result = coordinate variables position := by
  obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  exact (Finite.pure_success _ _ _ _ h).1

theorem parameter_meaning (variables position : Nat) (result : Form) (work left : Nat)
    (ok : (parameter variables position).run work = (.ok result,left)) (values : Valuation) :
    result.evaluate values = values position := by
  rw [parameter_value _ _ _ _ _ ok]
  exact coordinate_evaluate _ _ _

theorem scale_value (factor : Int) (a result : Form) (work left : Nat)
    (ok : (scale factor a).run work = (.ok result,left)) : result = a.scale factor := by
  obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  exact (Finite.pure_success _ _ _ _ h).1

theorem add_value (a b result : Form) (work left : Nat)
    (ok : (add a b).run work = (.ok result,left)) :
    result = a.add b ∧ a.coefficients.length = b.coefficients.length := by
  obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,guarded,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  exact ⟨(Finite.pure_success _ _ _ _ h).1,
    beq_iff_eq.mp (Finite.guard_success _ _ _ _ guarded).1⟩

theorem scale_meaning (factor : Int) (a result : Form) (work left : Nat)
    (ok : (scale factor a).run work = (.ok result,left)) (values : Valuation) :
    result.evaluate values = factor*a.evaluate values := by
  rw [scale_value _ _ _ _ _ ok]
  exact Form.evaluate_scale _ _ _

theorem add_meaning (a b result : Form) (work left : Nat)
    (ok : (add a b).run work = (.ok result,left)) (values : Valuation) :
    result.evaluate values = a.evaluate values+b.evaluate values := by
  obtain ⟨same,shape⟩ := add_value _ _ _ _ _ ok
  rw [same]
  exact Form.evaluate_add _ _ shape _

theorem sub_meaning (a b result : Form) (work left : Nat)
    (ok : (sub a b).run work = (.ok result,left)) (values : Valuation) :
    result.evaluate values = a.evaluate values-b.evaluate values := by
  obtain ⟨negative,middle,scaled,added⟩ := Finite.bind_success _ _ _ _ _ ok
  rw [add_meaning _ _ _ _ _ added,scale_meaning _ _ _ _ _ scaled]
  simp [Int.sub_eq_add_neg]

theorem isConstant_meaning (a : Form) (constant : isConstant a = true) (values : Valuation) :
    a.evaluate values = a.constant := by
  have zero := dot_zero a.coefficients constant values
  simp only [Form.evaluate,zero,Int.add_zero]

theorem multiply_meaning (a b result : Form) (work left : Nat)
    (ok : (multiply a b).run work = (.ok result,left)) (values : Valuation) :
    result.evaluate values = a.evaluate values*b.evaluate values := by
  obtain ⟨_,w₁,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  by_cases first : isConstant a = true
  · simp only [first,if_true] at h
    rw [scale_meaning _ _ _ _ _ h,isConstant_meaning a first values]
  · have firstFalse : isConstant a = false := Bool.eq_false_iff.mpr first
    by_cases second : isConstant b = true
    · simp only [firstFalse,second,if_true] at h
      rw [scale_meaning _ _ _ _ _ h,isConstant_meaning b second values]
      exact Int.mul_comm _ _
    · have secondFalse : isConstant b = false := Bool.eq_false_iff.mpr second
      simp only [firstFalse,secondFalse] at h
      cases h

end QleisliKernel.SourceTypes.NaturalAffine
