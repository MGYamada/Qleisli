import QleisliKernel.Qirf.EngineeringPure

/-! Bounded ordered pure tensor engineering composition.
Both components and both parent original artifacts are checked freshly. Exact
low-first tensors bind parents to the component matrices; the parent gap is
never subjected to a whole-matrix Frobenius check. Returned data are internal
engineering data, including when the exact sum budget is zero. No accepted
handle, serialized receipt, source-preservation, capability, cleanup, resource
or constitutional authority follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Finite.Basis

/-- Preserve the complete left and right prefix trees, including Unit. -/
def pair (left right : Semantics.Finite.Basis) : Semantics.Finite.Basis :=
  Atom.pair :: (left ++ right)

@[simp] theorem width_pair (left right : Semantics.Finite.Basis) :
    width (pair left right) = width left + width right := by
  simp [pair,width]

end QleisliKernel.Semantics.Finite.Basis

namespace QleisliKernel.Qirf.EngineeringPureTensor
open Semantics.Exact Semantics.Finite Finite

/-- Exactly two ordered components and exactly two independent parent roots.
The parent type trees are derived, rather than supplied as width-only claims. -/
structure Request where
  left : EngineeringPure.Request
  right : EngineeringPure.Request
  parentActual : EngineeringPure.LeafRequest
  parentIdeal : EngineeringPure.LeafRequest
  epsilon : Coefficient

def Request.domain (request : Request) : Basis :=
  Basis.pair request.left.domain request.right.domain

def Request.codomain (request : Request) : Basis :=
  Basis.pair request.left.codomain request.right.codomain

/-- These raw internal results have no exact cross-artifact handle conversion. -/
structure Checked where
  left : EngineeringPure.Checked
  right : EngineeringPure.Checked
  parentActual : PureLeaf.Checked
  parentIdeal : PureLeaf.Checked
  actualTensor : Matrix
  idealTensor : Matrix
  epsilon : Coefficient

/-- A single continuous checker-work chain. Scalar capacities and tensor
matrix capacities are the existing exact ones. There is no producer witness,
missing/extra component convention, or independent rerun of the parent gap. -/
def check (request : Request) : WorkM Checked := do
  let left ← EngineeringPure.check request.left
  let right ← EngineeringPure.check request.right
  let parentActual ← PureLeaf.check request.parentActual.artifact request.parentActual.order
    request.domain request.codomain request.parentActual.input request.parentActual.output
    request.parentActual.required
  let parentIdeal ← PureLeaf.check request.parentIdeal.artifact request.parentIdeal.order
    request.domain request.codomain request.parentIdeal.input request.parentIdeal.output
    request.parentIdeal.required
  let actualTensor ← exactWork (Exact.Matrix.tensorWork left.actual.actual right.actual.actual)
  exactWork (Exact.charge actualTensor.entries.length)
  guard (parentActual.actual == actualTensor) .equation
  let idealTensor ← exactWork (Exact.Matrix.tensorWork left.ideal.actual right.ideal.actual)
  exactWork (Exact.charge idealTensor.entries.length)
  guard (parentIdeal.actual == idealTensor) .equation
  exactWork (Exact.charge 128)
  let epsilon ← lift (arithmetic (Exact.Coefficient.add request.left.epsilon request.right.epsilon))
  guard (Exact.Coefficient.valid epsilon) .invalid
  guard (0 ≤ epsilon.numerator) .request
  guard (epsilon == request.epsilon) .equation
  return ⟨left,right,parentActual,parentIdeal,actualTensor,idealTensor,epsilon⟩

/-- Every component, root and tensor belongs to this actual execution. Guards
and the bounded dyadic addition retain their surrounding checker-work state. -/
structure Postcondition (request : Request) (checked : Checked) (work left : Nat) : Prop where
  execution : ∃ afterLeft afterRight afterParentActual afterParentIdeal
      afterActualTensor afterActualEquation afterIdealTensor afterIdealEquation,
    (EngineeringPure.check request.left).run work = (.ok checked.left,afterLeft) ∧
    (EngineeringPure.check request.right).run afterLeft = (.ok checked.right,afterRight) ∧
    (PureLeaf.check request.parentActual.artifact request.parentActual.order
      request.domain request.codomain request.parentActual.input request.parentActual.output
      request.parentActual.required).run afterRight = (.ok checked.parentActual,afterParentActual) ∧
    (PureLeaf.check request.parentIdeal.artifact request.parentIdeal.order
      request.domain request.codomain request.parentIdeal.input request.parentIdeal.output
      request.parentIdeal.required).run afterParentActual = (.ok checked.parentIdeal,afterParentIdeal) ∧
    (Exact.Matrix.tensorWork checked.left.actual.actual checked.right.actual.actual).run afterParentIdeal =
      (.ok checked.actualTensor,afterActualTensor) ∧
    (Exact.charge checked.actualTensor.entries.length).run afterActualTensor = (.ok (),afterActualEquation) ∧
    (Exact.Matrix.tensorWork checked.left.ideal.actual checked.right.ideal.actual).run afterActualEquation =
      (.ok checked.idealTensor,afterIdealTensor) ∧
    (Exact.charge checked.idealTensor.entries.length).run afterIdealTensor = (.ok (),afterIdealEquation) ∧
    (Exact.charge 128).run afterIdealEquation = (.ok (),left)
  actualEquation : checked.parentActual.actual = checked.actualTensor
  idealEquation : checked.parentIdeal.actual = checked.idealTensor
  epsilonAdd : Exact.Coefficient.add request.left.epsilon request.right.epsilon = .ok checked.epsilon
  epsilonValid : Exact.Coefficient.valid checked.epsilon = true
  epsilonNonnegative : 0 ≤ checked.epsilon.numerator
  requestedBudget : checked.epsilon = request.epsilon

theorem check_postcondition (request : Request) (checked : Checked) (work left : Nat)
    (ok : (check request).run work = (.ok checked,left)) :
    Postcondition request checked work left := by
  unfold check at ok
  obtain ⟨l,a,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨r,b,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨pa,c,hpa,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨pi,d,hpi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨ta,e,hat,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,ec,hActualCharge,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,f,hae,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨it,g,hit,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,gc,hIdealCharge,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,j,hie,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,k,hcharge,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨epsilon,m,hadd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,n,hvalid,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,p,hnonneg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,q,hrequested,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have remaining := (pure_success _ _ _ _ h).2
  subst checked
  subst left
  obtain ⟨actualEq,actualWork⟩ := guard_success _ _ _ _ hae
  obtain ⟨idealEq,idealWork⟩ := guard_success _ _ _ _ hie
  obtain ⟨added,additionWork⟩ := lift_success _ _ _ _ hadd
  obtain ⟨valid,validWork⟩ := guard_success _ _ _ _ hvalid
  obtain ⟨nonnegative,nonnegativeWork⟩ := guard_success _ _ _ _ hnonneg
  subst f
  subst j
  subst m
  subst n
  subst p
  obtain ⟨requested,requestedWork⟩ := guard_success _ _ _ _ hrequested
  subst q
  exact ⟨⟨a,b,c,d,e,ec,g,gc,hl,hr,hpa,hpi,
      exactWork_success _ _ _ _ hat,exactWork_success _ _ _ _ hActualCharge,
      exactWork_success _ _ _ _ hit,exactWork_success _ _ _ _ hIdealCharge,
      exactWork_success _ _ _ _ hcharge⟩,
    beq_iff_eq.mp actualEq,beq_iff_eq.mp idealEq,
    arithmetic_success _ _ added,valid,by simpa using nonnegative,beq_iff_eq.mp requested⟩

end QleisliKernel.Qirf.EngineeringPureTensor
