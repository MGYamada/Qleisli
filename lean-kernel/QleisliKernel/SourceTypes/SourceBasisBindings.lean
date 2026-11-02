import QleisliKernel.SourceTypes.GenericBasisInstance

/-! Complete per-body closing of original local basis obligations. Every entry
keeps its exact original index and actual closeBasis execution. Active entries
still require the corresponding BasisEvent's finite function and native code
equation; inactive entries retain the original false static-guard proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceBasisBindings
open Finite

structure Closed {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligations : List (GenericTypeTrace.BasisObligation sources)) (index : Fin obligations.length) where
  binding : GenericBasisInstance.Binding instantiation obligations[index]
  original : ∃ before after,
    (GenericBasisInstance.closeBasis instantiation obligations[index]).run before = (.ok binding,after)

structure Checked {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligations : List (GenericTypeTrace.BasisObligation sources)) where
  entries : List (Sigma (Closed instantiation obligations))
  ordered : entries.map (fun entry => entry.1.val) = List.range obligations.length
  uniqueOffsets : (obligations.map (·.offset)).Nodup

def prepare {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligations : List (GenericTypeTrace.BasisObligation sources)) :
    WorkM (Checked instantiation obligations) := do
  exactWork (Exact.charge (16*(obligations.length+1)^2))
  if uniqueOffsets : (obligations.map (·.offset)).Nodup then
    let entries ← (List.finRange obligations.length).mapM fun index => do
      let binding ← NaturalAffine.witness (GenericBasisInstance.closeBasis instantiation obligations[index])
      pure (⟨index,⟨binding.val,by with_reducible exact binding.property⟩⟩ : Sigma (Closed instantiation obligations))
    if ordered : entries.map (fun entry => entry.1.val) = List.range obligations.length then
      pure ⟨entries,ordered,uniqueOffsets⟩
    else throw .request
  else throw .request

structure ActiveAt {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligations : List (GenericTypeTrace.BasisObligation sources)) (offset : Nat) where
  index : Fin obligations.length
  closed : Closed instantiation obligations index
  originalOffset : obligations[index].offset = offset
  ports : GenericBasisInstance.Active instantiation obligations[index]
  active : closed.binding.status = .active ports

def activeAt {sources owner name original instantiation obligations}
    (checked : @Checked sources owner name original instantiation obligations) (offset : Nat) :
    WorkM (ActiveAt instantiation obligations offset) := do
  exactWork (Exact.charge (16*(obligations.length+checked.entries.length+1)))
  let some selected := checked.entries.find? (fun entry => obligations[entry.1].offset == offset) | throw .request
  if originalOffset : obligations[selected.1].offset = offset then
    match active : selected.2.binding.status with
    | .inactive _ => throw .request
    | .active ports => pure ⟨selected.1,selected.2,originalOffset,ports,active⟩
  else throw .request

/-- Only local events are counted: nested ordinary/static branch events stay
in their original caller; named callees discharge their own body obligations.
Every active original occurrence occurs once and every inactive one is absent. -/
def Checked.covered {sources owner name original instantiation obligations}
    (checked : @Checked sources owner name original instantiation obligations) (offsets : List Nat) : Bool :=
  checked.entries.all (fun entry =>
    let count := offsets.count obligations[entry.1].offset
    match entry.2.binding.status with
    | .inactive _ => count == 0
    | .active _ => count == 1) &&
      offsets.all (fun offset => checked.entries.any (fun entry => obligations[entry.1].offset == offset))

theorem ActiveAt.originalMember {sources owner name original instantiation obligations offset}
    (active : @ActiveAt sources owner name original instantiation obligations offset) :
    obligations[active.index] ∈ obligations := List.getElem_mem active.index.isLt

end QleisliKernel.SourceTypes.SourceBasisBindings
