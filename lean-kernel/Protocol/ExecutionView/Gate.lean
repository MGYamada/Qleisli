import Protocol.ExecutionView.Frame
import QleisliKernel.Finite

/-! Shared execution-view transport/error/work plumbing. Semantic acceptance
remains in each profile's existing core checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.Gate

inductive Error where
  | packet | invalidView | native (error : Finite.Error) | encoding | decodedView
  deriving BEq, DecidableEq, Repr

abbrev CheckM := ExceptT Error (StateM Nat)

def lift {α : Type} (result : Except Error α) : CheckM α :=
  match result with | .ok value => pure value | .error error => throw error

def native {α : Type} (action : Finite.WorkM α) : CheckM α := fun work =>
  let (result,left) := action.run work
  (result.mapError Error.native,left)

def guard (condition : Bool) (error : Error) : CheckM Unit :=
  if condition then pure () else throw error

theorem bind_run {α β : Type} (first : CheckM α) (next : α → CheckM β) (work : Nat) :
    (first >>= next).run work =
      match first.run work with
      | (.error error,left) => (.error error,left)
      | (.ok value,left) => (next value).run left := by
  simp only [ExceptT.run,bind,ExceptT.bind,ExceptT.mk,StateT.bind]
  cases first work with
  | mk result middle => cases result <;> rfl

theorem bind_success {α β : Type} (first : CheckM α) (next : α → CheckM β)
    (work left : Nat) (value : β) (ok : (first >>= next).run work = (.ok value,left)) :
    ∃ intermediate middle, first.run work = (.ok intermediate,middle) ∧
      (next intermediate).run middle = (.ok value,left) := by
  rw [bind_run] at ok
  cases h : first.run work with
  | mk result middle =>
    rw [h] at ok
    cases result with
    | error error => cases ok
    | ok intermediate => exact ⟨intermediate,middle,rfl,ok⟩

theorem native_success {α : Type} (action : Finite.WorkM α) (result : α)
    (work left : Nat) (ok : (native action).run work = (.ok result,left)) :
    action.run work = (.ok result,left) := by
  change ((action.run work).1.mapError Error.native,(action.run work).2) = (.ok result,left) at ok
  cases h : action.run work with
  | mk value middle =>
    rw [h] at ok
    cases value <;> simp_all [Except.mapError]

theorem lift_success {α : Type} (input : Except Error α) (result : α)
    (work left : Nat) (ok : (lift input).run work = (.ok result,left)) :
    input = .ok result ∧ left = work := by
  cases input with
  | error error => cases ok
  | ok value => cases ok; exact ⟨rfl,rfl⟩

theorem guard_success (condition : Bool) (error : Error) (work left : Nat)
    (ok : (guard condition error).run work = (.ok (),left)) :
    condition = true ∧ left = work := by
  unfold guard at ok
  cases condition with
  | false => cases ok
  | true => cases ok; exact ⟨rfl,rfl⟩

end QleisliKernel.Protocol.ExecutionView.Gate
