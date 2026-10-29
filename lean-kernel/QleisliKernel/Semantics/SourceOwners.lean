import QleisliKernel.Semantics.FiniteCarrier

/-! Linear source owner identities and structural tuples. A quantum owner of
a product basis is one atom; it is never an implicitly destructured tuple.
These reference predicates import no source parser or acceptance checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceOwners

structure Owner where
  ordinal : Nat
  basis : FiniteCarrier.Basis
  deriving BEq, DecidableEq, Repr

inductive Atom where
  | owner (value : Owner)
  | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Value := List Atom

structure Cell where
  name : String
  value : Value
  deriving BEq, DecidableEq, Repr

abbrev Environment := List Cell

def valueOwners (value : Value) : List Owner :=
  value.filterMap fun atom => match atom with | .owner owner => some owner | .tuple _ => none

def owners (environment : Environment) : List Owner :=
  environment.flatMap fun cell => valueOwners cell.value

def Conserved (initial current : Environment) : Prop :=
  (owners initial).Perm (owners current)

inductive Move : Environment → String → Value → Environment → Prop
  | head (name value rest) : Move (⟨name,value⟩ :: rest) name value rest
  | tail (cell before name value after) (different : cell.name ≠ name)
      (moved : Move before name value after) : Move (cell :: before) name value (cell :: after)


/-- Moving a source name transfers the exact logical owner tokens, including
their complete basis trees; physical width plays no role. -/
theorem Move.ownerPartition {before name value after} (moved : Move before name value after) :
    (owners before).Perm (valueOwners value ++ owners after) := by
  induction moved with
  | head => exact .refl _
  | tail cell before name value after different moved ih =>
    change (valueOwners cell.value ++ owners before).Perm
      (valueOwners value ++ (valueOwners cell.value ++ owners after))
    exact (ih.append_left _).trans (List.perm_append_comm_assoc _ _ _)

end QleisliKernel.Semantics.SourceOwners
