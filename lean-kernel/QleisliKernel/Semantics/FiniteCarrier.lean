import QleisliKernel.Semantics.Exact

/-! Finite ordinary-carrier descriptions for #64. Logical cardinality, nominal
identity and physical code coordinates are separate. These data confer no
acceptance, inverse/control access or source-preservation claim. Native/source
integration remains pending; the existing physical Raw types are unchanged.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.FiniteCarrier

/-- Original source identity is retained as bytes, not a foreign numeric DefId
or a width. Binding the description to source elaboration is a separate duty. -/
structure Origin where
  moduleName : String
  declarationName : String
  source : String
  deriving BEq, DecidableEq, Repr

/-- Prefix tree. Record children follow in declared field order; a zero-field
record is a singleton, distinct from Unit, Bits<0> and a singleton enum. -/
inductive Atom where
  | unit | bit | bits (width : Nat) | pair | tuple (arity : Nat)
  | enumeration (origin : Origin) (variants : List String)
  | record (origin : Origin) (fields : List String)
  deriving BEq, DecidableEq, Repr

abbrev Basis := List Atom

structure Layout where
  bits : Nat
  labels : List Nat
  deriving BEq, DecidableEq, Repr

def singleton : Layout := ⟨0,[0]⟩

/-- The first component occupies low physical axes and varies fastest in the
logical product order. No tuple reassociation or owner split is inferred. -/
def tensor (first second : Layout) : Layout :=
  ⟨first.bits + second.bits,
    second.labels.flatMap fun high => first.labels.map fun low => low + 2^first.bits * high⟩

def tagBits (count : Nat) : Nat := if count ≤ 1 then 0 else Nat.log2 (count - 1) + 1

def children : Atom → Option Nat
  | .pair => some 2
  | .tuple arity => some arity
  | .record _ fields => some fields.length
  | _ => none

def leaf : Atom → Option Layout
  | .unit => some singleton
  | .bit => some ⟨1,[0,1]⟩
  | .bits width => some ⟨width,List.range (2^width)⟩
  | .enumeration _ variants =>
    if variants.isEmpty then none else some ⟨tagBits variants.length,List.range variants.length⟩
  | _ => none

/-- Independent interpretation of the complete prefix tree, without checker
policy or producer decisions. Callers bound inputs before evaluating it. -/
def layoutStep (atom : Atom) (pending : Option (List Layout)) : Option (List Layout) := do
  let stack ← pending
  match children atom with
  | none => return (← leaf atom) :: stack
  | some arity =>
    if arity > stack.length then none
    else some ((stack.take arity).foldl tensor singleton :: stack.drop arity)

def layout (basis : Basis) : Option Layout := do
  let [result] ← basis.foldr layoutStep (some []) | none
  return result

def dimension (basis : Basis) : Option Nat := (layout basis).map (·.labels.length)

def encoding (code : Layout) : Exact.Matrix :=
  let rows := 2^code.bits
  let cols := code.labels.length
  ⟨rows,cols,(List.range (rows*cols)).map fun index =>
    if code.labels[index % cols]? == some (index / cols) then Exact.Scalar.one else Exact.Scalar.zero⟩

deriving instance ReflBEq, LawfulBEq for Origin, Atom, Layout

end QleisliKernel.Semantics.FiniteCarrier
