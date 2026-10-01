import QleisliKernel.Raw.Function
import QleisliKernel.Raw.Protected

/-! Pure raw checking without a global dense matrix. Only broad certified scopes
use the existing local six-bit equation checker. Protected scopes retain the
twelve-bit structural profile and their original uses.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Pure
open Semantics.Exact Semantics.Finite Semantics.Raw Semantics.Function Finite

def eventCheck (dependencies : List Dependency) : Event → WorkM Unit
  | .circuit bits steps => guard (circuitStepsValid (dependencies.map (·.signature)) bits steps)
  | .init0 _ => pure ()
  | .liftBasis before after inputAxes outputAxes table =>
    guard (axesValid before inputAxes && axesValid after outputAxes &&
      tableValid inputAxes.length outputAxes.length table true)
  | .reorder bits axes => guard (axesValid bits axes && axes.length == bits)
  | .computed _ axes sourceBits ancillaBits function uses logical => do
    let _ ← clean dependencies sourceBits axes.length ancillaBits function uses logical
    return ()
  | .protectedComputed _ axes sourceBits ancillaBits function uses =>
    guard (sourceBits ≤ axes.length && tableValid sourceBits ancillaBits function false &&
      usesValid sourceBits ancillaBits (axes.length-sourceBits) uses)

def verify (dependencies : List Dependency) (program : Program) : WorkM Prepared := do
  exactWork (Exact.charge (rawFields program))
  let prepared ← lift (prepare (dependencies.map (·.signature)) program)
  let _ ← prepared.events.foldlM (fun _ event => eventCheck dependencies event) ()
  return prepared

structure Checked where
  receipts : List Receipt
  program : Program
  prepared : Prepared
  deriving Repr

/-- Complete dependency graph reconstruction precedes general pure checking.
There is no externally supplied receipt or global six-qubit restriction. -/
def inspect (inputs : List Input) (bindings : List Binding) (program : Program) : WorkM Checked := do
  let receipts ← Function.checkAll inputs bindings
  let prepared ← verify (receipts.map Receipt.dependency) program
  return ⟨receipts,program,prepared⟩

private theorem events_checked (dependencies : List Dependency) (events : List Event) (work left : Nat)
    (ok : (events.foldlM (fun _ event => eventCheck dependencies event) ()).run work = (.ok (),left)) :
    ∀ event ∈ events, ∃ a b, (eventCheck dependencies event).run a = (.ok (),b) := by
  induction events generalizing work with
  | nil => simp
  | cons event events ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    cases next
    intro chosen member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨work,middle,hn⟩
    · exact ih middle hr chosen member

theorem verify_conditions (dependencies : List Dependency) (program : Program) (prepared : Prepared)
    (work left : Nat) (ok : (verify dependencies program).run work = (.ok prepared,left)) :
    prepare (dependencies.map (·.signature)) program = .ok prepared ∧
    Semantics.RawTrace.run program = some prepared.reference ∧
    ∀ event ∈ prepared.events, ∃ a b, (eventCheck dependencies event).run a = (.ok (),b) := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,w₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst prepared
  have original := (lift_success _ _ _ _ hp).1
  exact ⟨original,prepare_reference _ _ _ original,events_checked _ _ _ _ he⟩

theorem inspect_fresh (inputs : List Input) (bindings : List Binding) (program : Program)
    (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program).run work = (.ok checked,left)) :
    checked.program = program ∧ ∃ a b c d,
      (Function.checkAll inputs bindings).run a = (.ok checked.receipts,b) ∧
      (verify (checked.receipts.map Receipt.dependency) program).run c = (.ok checked.prepared,d) := by
  obtain ⟨receipts,middle,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨prepared,after,hv,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  exact ⟨rfl,work,middle,middle,after,hc,hv⟩

end QleisliKernel.Raw.Pure
