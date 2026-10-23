import QleisliKernel.Semantics.OrdinaryValue

/-! Shape-preserving ordinary storage transport.
This independent relation preserves each nominal and zero-width node. It is
neither a new IR nor an acceptance predicate. The generic lookup premise is
discharged against actual simultaneous phi semantics in the separate bridge.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Semantics.OrdinaryValue
open FiniteCarrier

/-- Ordered leaf correspondence; source identities need not be distinct.
Reading one ordinary value into several destinations is ordinary copying. -/
inductive IdsTransport (relation : Nat → Nat → Prop) : List Nat → List Nat → Prop
  | nil : IdsTransport relation [] []
  | cons (source target sources targets) (head : relation source target)
      (tail : IdsTransport relation sources targets) :
      IdsTransport relation (source :: sources) (target :: targets)

theorem IdsTransport.lengths {relation : Nat → Nat → Prop} {sources targets : List Nat}
    (moved : IdsTransport relation sources targets) : sources.length = targets.length := by
  induction moved with
  | nil => rfl
  | cons source target sources targets head tail ih => simpa using congrArg Nat.succ ih

mutual
  /-- Exact tree transport, not equality of flattened coordinates. In particular,
  Unit, Bits 0, singleton enums and empty records retain different nodes. -/
  inductive StorageTransport (relation : Nat → Nat → Prop) : Storage → Storage → Prop
    | unit : StorageTransport relation .unit .unit
    | bit (source target) (edge : relation source target) :
        StorageTransport relation (.bit source) (.bit target)
    | bits (sources targets) (edges : IdsTransport relation sources targets) :
        StorageTransport relation (.bits sources) (.bits targets)
    | pair (left right outLeft outRight)
        (first : StorageTransport relation left outLeft)
        (second : StorageTransport relation right outRight) :
        StorageTransport relation (.pair left right) (.pair outLeft outRight)
    | tuple (sources targets) (items : StoresTransport relation sources targets) :
        StorageTransport relation (.tuple sources) (.tuple targets)
    | enumeration (origin : Origin) (sources targets)
        (edges : IdsTransport relation sources targets) :
        StorageTransport relation (.enumeration origin sources) (.enumeration origin targets)
    | record (origin : Origin) (sources targets)
        (fields : FieldsTransport relation sources targets) :
        StorageTransport relation (.record origin sources) (.record origin targets)
  inductive StoresTransport (relation : Nat → Nat → Prop) : List Storage → List Storage → Prop
    | nil : StoresTransport relation [] []
    | cons (source target sources targets) (head : StorageTransport relation source target)
        (tail : StoresTransport relation sources targets) :
        StoresTransport relation (source :: sources) (target :: targets)
  /-- The same field name occurs at the same position on both sides. No zip
  truncation, field permutation or zero-width omission can construct this rule. -/
  inductive FieldsTransport (relation : Nat → Nat → Prop) :
      List (String × Storage) → List (String × Storage) → Prop
    | nil : FieldsTransport relation [] []
    | cons (name : String) (source target sources targets)
        (head : StorageTransport relation source target)
        (tail : FieldsTransport relation sources targets) :
        FieldsTransport relation ((name,source) :: sources) ((name,target) :: targets)
end

theorem FieldsTransport.names {relation : Nat → Nat → Prop}
    {sources targets : List (String × Storage)}
    (moved : FieldsTransport relation sources targets) :
    sources.map Prod.fst = targets.map Prod.fst := by
  cases moved with
  | nil => rfl
  | cons name source target sources targets head tail =>
    simpa using congrArg (List.cons name) tail.names

/-- Each observed source leaf retains its bit at its corresponding target.
This is an explicit semantic premise, not a checker or solver success claim. -/
def LookupAlong (relation : Nat → Nat → Prop) (before after : Valuation) : Prop :=
  ∀ source target, relation source target →
    ∀ bit, lookup before source = some bit → lookup after target = some bit

theorem Reads.transport {relation : Nat → Nat → Prop} {before after : Valuation}
    {sources targets : List Nat} {bits : List Bool}
    (read : Reads before sources bits) (moved : IdsTransport relation sources targets)
    (bound : LookupAlong relation before after) : Reads after targets bits := by
  induction read generalizing targets with
  | nil => cases moved; exact .nil
  | cons source bit sources bits head tail ih =>
    cases moved with
    | cons source target sources targets edge rest =>
      exact .cons target bit targets bits (bound source target edge bit head) (ih rest)

/-- Representation records cannot lose trailing zero-width stores through zip. -/
theorem RepresentsMany.storage_lengths {values : Valuation} {bases : List Basis}
    {items : List Value} {stores : List Storage}
    (represented : RepresentsMany values bases items stores) : bases.length = stores.length := by
  cases represented with
  | nil => rfl
  | cons basis value storage bases items stores head tail =>
    simpa using congrArg Nat.succ tail.storage_lengths

/-- Recover a complete target store list from ordered named-field transport.
The explicit arity premise prevents the shorter-zip loophole. -/
theorem FieldsTransport.zip_sources {relation : Nat → Nat → Prop} {names : List String}
    {stores : List Storage} {targets : List (String × Storage)}
    (moved : FieldsTransport relation (names.zip stores) targets)
    (arity : names.length = stores.length) :
    ∃ output, targets = names.zip output ∧ StoresTransport relation stores output := by
  induction names generalizing stores targets with
  | nil =>
    cases stores with
    | nil => cases moved; exact ⟨[],rfl,.nil⟩
    | cons head tail => simp at arity
  | cons name names ih =>
    cases stores with
    | nil => simp at arity
    | cons source stores =>
      change FieldsTransport relation ((name,source) :: names.zip stores) targets at moved
      cases moved with
      | cons name source target sources targets head tail =>
        have restArity : names.length = stores.length := Nat.succ.inj arity
        obtain ⟨output,same,rest⟩ := ih tail restArity
        exact ⟨target :: output,by simp [same],.cons source target stores output head rest⟩

/-- Transport preserves the complete Basis and logical Value, hence nominal
identity, enum range, exact bits, field order and all zero-width structure. -/
theorem Represents.transport {relation : Nat → Nat → Prop} {before after : Valuation}
    {basis : Basis} {value : Value} {source : Storage}
    (represented : Represents before basis value source)
    (bound : LookupAlong relation before after)
    {target : Storage} (moved : StorageTransport relation source target) :
    Represents after basis value target := by
  revert target
  change ∀ target : Storage, StorageTransport relation source target →
    Represents after basis value target
  induction represented using Represents.rec
      (motive_2 := fun bases items stores _ =>
        ∀ targets, StoresTransport relation stores targets → RepresentsMany after bases items targets) with
  | unit => intro target moved; cases moved; exact .unit
  | bit id bit present =>
    intro target moved
    cases moved with
    | bit source target edge => exact .bit target bit (bound id target edge bit present)
  | bits ids bits read =>
    intro target moved
    cases moved with
    | bits sources targets edges =>
      have kept := Represents.bits targets bits (read.transport edges bound)
      simpa only [← edges.lengths] using kept
  | pair a b x y sx sy left right ihLeft ihRight =>
    intro target moved
    cases moved with
    | pair left right outLeft outRight first second =>
      exact .pair a b x y outLeft outRight (ihLeft outLeft first) (ihRight outRight second)
  | tuple bases items storage represented ih =>
    intro target moved
    cases moved with
    | tuple sources targets related => exact .tuple bases items targets (ih targets related)
  | enumeration origin variants ordinal ids bits range width read encoded =>
    intro target moved
    cases moved with
    | enumeration origin sources targets edges =>
      exact .enumeration origin variants ordinal targets bits range
        (edges.lengths.symm.trans width) (read.transport edges bound) encoded
  | record origin names bases items storage arity represented ih =>
    intro target moved
    cases moved with
    | record origin sources targets fields =>
      obtain ⟨outputs,same,related⟩ := fields.zip_sources (arity.trans represented.storage_lengths)
      rw [same]
      exact .record origin names bases items outputs arity (ih outputs related)
  | nil =>
    rename_i targets moved
    cases moved
    exact .nil
  | cons basis value storage bases items stores head tail ihHead ihTail =>
    rename_i targets moved
    cases moved with
    | cons source target sources targets first rest =>
      exact .cons basis value target bases items targets (ihHead target first) (ihTail targets rest)

end QleisliKernel.Semantics.OrdinaryValue
