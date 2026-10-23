import QleisliKernel.Semantics.FiniteCarrier

/-! Independent ordinary-value interpretation for the finite carrier.
These definitions relate typed logical values to classical history bindings.
They do not accept programs or establish original-source authorization,
typed runtime replay, source preservation or a new guarantee.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Semantics.OrdinaryValue
open FiniteCarrier

abbrev Valuation := List (Nat × Bool)

/-- The same first-binding lookup used by the actual RawInstrument histories.
Freshness and lexical accessibility remain separate original Raw obligations. -/
def lookup (values : Valuation) (id : Nat) : Option Bool :=
  (values.find? (fun pair => pair.1 == id)).map (·.2)

/-- Low-coordinate-first order, agreeing with FiniteCarrier.tensor. -/
def littleEndian (bits : List Bool) : Nat :=
  bits.foldr (fun bit rest => (if bit then 1 else 0) + 2 * rest) 0

/-- Ordinary logical values contain neither a quantum owner nor a state vector.
In particular, a zero-width ordinary value is not an empty quantum owner. -/
inductive Value where
  | unit
  | bit (value : Bool)
  | bits (values : List Bool)
  | pair (first second : Value)
  | tuple (values : List Value)
  | enumeration (origin : Origin) (ordinal : Nat)
  | record (origin : Origin) (fields : List (String × Value))

/-- Ordinary storage names actual classical SSA identities. Structural nodes,
including zero-width nodes, cannot be replaced by an untyped list of bits. -/
inductive Storage where
  | unit
  | bit (id : Nat)
  | bits (ids : List Nat)
  | pair (first second : Storage)
  | tuple (values : List Storage)
  | enumeration (origin : Origin) (ids : List Nat)
  | record (origin : Origin) (fields : List (String × Storage))

inductive Reads (values : Valuation) : List Nat → List Bool → Prop
  | nil : Reads values [] []
  | cons (id bit ids bits) (head : lookup values id = some bit)
      (tail : Reads values ids bits) : Reads values (id :: ids) (bit :: bits)

theorem Reads.lengths {values ids bits} (read : Reads values ids bits) :
    ids.length = bits.length := by
  induction read with
  | nil => rfl
  | cons id bit ids bits head tail ih => simpa using congrArg Nat.succ ih

theorem Reads.unique {values ids first second} (left : Reads values ids first)
    (right : Reads values ids second) : first = second := by
  cases left with
  | nil => cases right; rfl
  | cons id bit ids bits head tail =>
    cases right with
    | cons id other ids others otherHead otherTail =>
      have same : bit = other := Option.some.inj (head.symm.trans otherHead)
      rw [same,tail.unique otherTail]

/-- Existing bindings keep their actual values. This does not assert that new
bindings are fresh, in scope, or authorized by any instruction. -/
def Extends (before after : Valuation) : Prop :=
  ∀ id bit, lookup before id = some bit → lookup after id = some bit

theorem append_extends (before extra : Valuation) : Extends before (before ++ extra) := by
  intro id bit bound
  unfold lookup at bound ⊢
  rw [List.find?_append]
  cases found : before.find? (fun pair => pair.1 == id) with
  | none => simp [found] at bound
  | some pair => simpa [found] using bound

theorem lookup_append_fresh {before : Valuation} {id : Nat} (bit : Bool)
    (fresh : lookup before id = none) : lookup (before ++ [(id,bit)]) id = some bit := by
  unfold lookup at fresh ⊢
  rw [List.find?_append]
  cases found : before.find? (fun pair => pair.1 == id) with
  | none => simp [List.find?]
  | some pair => simp [found] at fresh

theorem Reads.extends {before after ids bits} (read : Reads before ids bits)
    (preserved : Extends before after) : Reads after ids bits := by
  induction read with
  | nil => exact .nil
  | cons id bit ids bits head tail ih =>
    exact .cons id bit ids bits (preserved id bit head) ih

mutual
  /-- Logical typing over the existing prefix carrier, independent of storage,
  layout reconstruction, checker success and original-source authorization. -/
  inductive ValueOf : Basis → Value → Prop
    | unit : ValueOf [.unit] .unit
    | bit (bit : Bool) : ValueOf [.bit] (.bit bit)
    | bits (width : Nat) (bits : List Bool) (sized : bits.length = width) :
        ValueOf [.bits width] (.bits bits)
    | pair (a b : Basis) (x y : Value) (left : ValueOf a x) (right : ValueOf b y) :
        ValueOf (.pair :: (a ++ b)) (.pair x y)
    | tuple (bases : List Basis) (values : List Value) (items : ValuesOf bases values) :
        ValueOf (.tuple bases.length :: bases.flatten) (.tuple values)
    | enumeration (origin : Origin) (variants : List String) (ordinal : Nat)
        (range : ordinal < variants.length) :
        ValueOf [.enumeration origin variants] (.enumeration origin ordinal)
    | record (origin : Origin) (names : List String) (bases : List Basis)
        (values : List Value) (arity : names.length = bases.length)
        (items : ValuesOf bases values) :
        ValueOf (.record origin names :: bases.flatten) (.record origin (names.zip values))
  inductive ValuesOf : List Basis → List Value → Prop
    | nil : ValuesOf [] []
    | cons (basis value bases values) (head : ValueOf basis value)
        (tail : ValuesOf bases values) : ValuesOf (basis :: bases) (value :: values)
end

theorem ValuesOf.lengths {bases values} (typed : ValuesOf bases values) :
    bases.length = values.length := by
  cases typed with
  | nil => rfl
  | cons basis value bases values head tail => simpa using congrArg Nat.succ tail.lengths

/-- Exact field names and their declaration order survive even when some
children have no physical coordinates. No field may disappear through zip. -/
theorem ValueOf.record_names {origin names tail fields}
    (typed : ValueOf (.record origin names :: tail) (.record origin fields)) :
    fields.map Prod.fst = names := by
  cases typed with
  | record origin names bases values arity items =>
    exact List.map_fst_zip (Nat.le_of_eq (arity.trans items.lengths))

mutual
  /-- A typed logical value agrees with actual classical history bindings.
  Enum range is stricter than physical tag width; nominal identity and record
  field order are exact. Repeated SSA reads are ordinary copying, not new owners. -/
  inductive Represents (values : Valuation) : Basis → Value → Storage → Prop
    | unit : Represents values [.unit] .unit .unit
    | bit (id bit) (bound : lookup values id = some bit) :
        Represents values [.bit] (.bit bit) (.bit id)
    | bits (ids bits) (read : Reads values ids bits) :
        Represents values [.bits ids.length] (.bits bits) (.bits ids)
    | pair (a b : Basis) (x y : Value) (sx sy : Storage)
        (left : Represents values a x sx) (right : Represents values b y sy) :
        Represents values (.pair :: (a ++ b)) (.pair x y) (.pair sx sy)
    | tuple (bases : List Basis) (items : List Value) (storage : List Storage)
        (represented : RepresentsMany values bases items storage) :
        Represents values (.tuple bases.length :: bases.flatten) (.tuple items) (.tuple storage)
    | enumeration (origin : Origin) (variants : List String) (ordinal : Nat)
        (ids : List Nat) (bits : List Bool) (range : ordinal < variants.length)
        (width : ids.length = tagBits variants.length) (read : Reads values ids bits)
        (encoded : littleEndian bits = ordinal) :
        Represents values [.enumeration origin variants]
          (.enumeration origin ordinal) (.enumeration origin ids)
    | record (origin : Origin) (names : List String) (bases : List Basis)
        (items : List Value) (storage : List Storage) (arity : names.length = bases.length)
        (represented : RepresentsMany values bases items storage) :
        Represents values (.record origin names :: bases.flatten)
          (.record origin (names.zip items)) (.record origin (names.zip storage))
  inductive RepresentsMany (values : Valuation) : List Basis → List Value → List Storage → Prop
    | nil : RepresentsMany values [] [] []
    | cons (basis value storage bases items stores) (head : Represents values basis value storage)
        (tail : RepresentsMany values bases items stores) :
        RepresentsMany values (basis :: bases) (value :: items) (storage :: stores)
end

theorem Represents.typed {values basis value storage}
    (represented : Represents values basis value storage) : ValueOf basis value := by
  induction represented using Represents.rec
      (motive_2 := fun bases items _ _ => ValuesOf bases items) with
  | unit => exact .unit
  | bit id bit bound => exact .bit bit
  | bits ids bits read => exact .bits ids.length bits read.lengths.symm
  | pair a b x y sx sy left right ihLeft ihRight => exact .pair a b x y ihLeft ihRight
  | tuple bases items storage represented ih => exact .tuple bases items ih
  | enumeration origin variants ordinal ids bits range width read encoded =>
    exact .enumeration origin variants ordinal range
  | record origin names bases items storage arity represented ih =>
    exact .record origin names bases items arity ih
  | nil => exact .nil
  | cons basis value storage bases items stores head tail ihHead ihTail =>
    exact .cons basis value bases items ihHead ihTail

theorem RepresentsMany.typed {values bases items storage}
    (represented : RepresentsMany values bases items storage) : ValuesOf bases items := by
  cases represented with
  | nil => exact .nil
  | cons basis value storage bases items stores head tail =>
    exact .cons basis value bases items head.typed tail.typed

theorem Represents.extends {before after basis value storage}
    (represented : Represents before basis value storage) (preserved : Extends before after) :
    Represents after basis value storage := by
  induction represented using Represents.rec
      (motive_2 := fun bases items storage _ => RepresentsMany after bases items storage) with
  | unit => exact .unit
  | bit id bit bound => exact .bit id bit (preserved id bit bound)
  | bits ids bits read => exact .bits ids bits (read.extends preserved)
  | pair a b x y sx sy left right ihLeft ihRight =>
    exact .pair a b x y sx sy ihLeft ihRight
  | tuple bases items storage represented ih =>
    exact .tuple bases items storage ih
  | enumeration origin variants ordinal ids bits range width read encoded =>
    exact .enumeration origin variants ordinal ids bits range width (read.extends preserved) encoded
  | record origin names bases items storage arity represented ih =>
    exact .record origin names bases items storage arity ih
  | nil => exact .nil
  | cons basis value storage bases items stores head tail ihHead ihTail =>
    exact .cons basis value storage bases items stores ihHead ihTail

theorem RepresentsMany.extends {before after bases items storage}
    (represented : RepresentsMany before bases items storage) (preserved : Extends before after) :
    RepresentsMany after bases items storage := by
  cases represented with
  | nil => exact .nil
  | cons basis value storage bases items stores head tail =>
    exact .cons basis value storage bases items stores (head.extends preserved) (tail.extends preserved)

/-- Copy shares classical identities and retains both complete ordinary trees.
There is no corresponding rule for Raw.Port or a quantum owner token. -/
theorem Represents.copy {values basis value storage}
    (represented : Represents values basis value storage) :
    Represents values (.pair :: (basis ++ basis)) (.pair value value) (.pair storage storage) :=
  .pair basis basis value value storage storage represented represented

/-- Projection is positional only after a separate original-source member rule
has established this exact declaration index, name, visibility and type. -/
theorem RepresentsMany.get {values bases items stores}
    (represented : RepresentsMany values bases items stores) (index : Nat)
    {basis value storage} (typeAt : bases[index]? = some basis)
    (valueAt : items[index]? = some value) (storageAt : stores[index]? = some storage) :
    Represents values basis value storage := by
  cases represented with
  | nil => simp at typeAt
  | cons headType headValue headStorage tailTypes tailValues tailStorage head tail =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at typeAt valueAt storageAt
      subst basis
      subst value
      subst storage
      exact head
    | succ index =>
      exact tail.get index typeAt valueAt storageAt

theorem ValueOf.enum_range {origin variants ordinal}
    (typed : ValueOf [.enumeration origin variants] (.enumeration origin ordinal)) :
    ordinal < variants.length := by
  cases typed with
  | enumeration origin variants ordinal range => exact range

theorem ValueOf.enum_identity {wanted actual variants ordinal}
    (typed : ValueOf [.enumeration wanted variants] (.enumeration actual ordinal)) :
    wanted = actual := by
  cases typed
  rfl

end QleisliKernel.Semantics.OrdinaryValue
