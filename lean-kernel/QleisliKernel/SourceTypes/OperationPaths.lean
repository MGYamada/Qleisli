import Std

/-! Existing separate operation access interfaces, with no source lookup,
effect inference or body/implementation acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OperationPaths

structure Paths where
  applicable : Bool
  adjointable : Bool
  controllable : Bool
  deriving BEq, DecidableEq, Repr

def Paths.meet (left right : Paths) : Paths :=
  ⟨left.applicable && right.applicable,left.adjointable && right.adjointable,
    left.controllable && right.controllable⟩

def Paths.join (left right : Paths) : Paths :=
  ⟨left.applicable || right.applicable,left.adjointable || right.adjointable,
    left.controllable || right.controllable⟩

def Paths.any (paths : Paths) : Bool := paths.applicable || paths.adjointable || paths.controllable

/-- Path propagation depends on constructor shape and original formal
prerequisites, independently of selected widths, Meaning or repetition count.
Concrete and symbolic adapters must supply their authenticated child edges. -/
inductive Shape where
  | leaf
  | provider (actuals : List (Nat × Paths))
  | formal (actuals : List (Nat × Paths)) (selectedPosition : Option Nat)
  | inverse (child : Nat)
  | controlled (child : Nat)
  | repeat (child : Nat)
  | pair (left right : Nat)
  | conjugate (outer middle : Nat)

def Shape.children (shape : Shape) (requested : Paths) : List (Nat × Paths) :=
  match shape with
  | .leaf => []
  | .provider actuals =>
    let reverse : Paths := if requested.adjointable then ⟨true,true,false⟩ else ⟨false,false,false⟩
    let control : Paths := if requested.controllable then ⟨true,true,true⟩ else ⟨false,false,false⟩
    actuals.map fun (index,premises) => (index,premises.join (reverse.join control))
  | .formal actuals selected =>
    -- The selected formal is an occurrence position, not a child node index:
    -- two original actuals may point to one shared description node.
    actuals.zipIdx.map fun ((index,premises),position) =>
      (index,premises.join (if selected == some position then requested else ⟨false,false,false⟩))
  | .inverse child => [(child,⟨requested.adjointable,true,requested.controllable⟩)]
  | .controlled child => [(child,if requested.any then ⟨false,false,true⟩ else ⟨false,false,false⟩)]
  | .repeat child => [(child,requested)]
  | .pair left right => [(left,requested),(right,requested)]
  | .conjugate outer middle =>
    [(outer,if requested.any then ⟨true,true,false⟩ else ⟨false,false,false⟩),(middle,requested)]

end QleisliKernel.SourceTypes.OperationPaths
