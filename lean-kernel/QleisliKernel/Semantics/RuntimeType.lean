import QleisliKernel.Semantics.FiniteCarrier

/-! Complete runtime type shape over the existing ordinary finite universe.
Q is one explicit owner node, including for a zero-width basis. Ordinary
products may contain separate owners; a record's fields and a Q node's basis
remain ordinary. This reference imports no parser or acceptance checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.RuntimeType

inductive Atom where
  | finite (value : FiniteCarrier.Atom)
  | quantum
  deriving BEq, DecidableEq, Repr

abbrev Tree := List Atom

def ordinary (basis : FiniteCarrier.Basis) : Tree := basis.map .finite

def owner (basis : FiniteCarrier.Basis) : Tree := .quantum :: ordinary basis

def tuple (arity : Nat) (fields : List Tree) : Tree :=
  .finite (if arity == 2 then .pair else .tuple arity) :: fields.flatten

structure Shape where
  basis : Option FiniteCarrier.Basis
  owners : List FiniteCarrier.Basis
  deriving BEq, DecidableEq, Repr

/-- Ordinary products retain their complete source tree. A tuple of owners is
not the basis of one owner, even when both have the same physical width. -/
def step (atom : Atom) (pending : Option (List Shape)) : Option (List Shape) := do
  let stack ← pending
  match atom with
  | .quantum =>
    let child :: rest := stack | none
    let some basis := child.basis | none
    return ⟨none,[basis]⟩ :: rest
  | .finite node =>
    match FiniteCarrier.children node with
    | none => return ⟨some [node],[]⟩ :: stack
    | some arity =>
      if arity > stack.length then none else do
        let fields := stack.take arity
        let basis := fields.foldlM (fun result field => do
          return result ++ (← field.basis)) []
        match node with
        | .record _ _ => if basis.isNone then none else pure ()
        | .pair => pure ()
        | .tuple count => if count < 3 then none else pure ()
        | _ => none
        return ⟨basis.map (node :: ·),fields.flatMap (·.owners)⟩ :: stack.drop arity

def shape (ty : Tree) : Option Shape := do
  let [result] ← ty.foldr step (some []) | none
  return result

def ownerBases (ty : Tree) : Option (List FiniteCarrier.Basis) :=
  (shape ty).map (·.owners)

end QleisliKernel.Semantics.RuntimeType
