import QleisliKernel.Qirf.RuntimeOrdinaryPhis

/-! Both operand snapshots and simultaneous phi reads, without new source
grammar, dense quantum objects or a native accepted request.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinaryPhis
open QleisliKernel QleisliKernel.Qirf.RuntimeOrdinarySSA
open QleisliKernel.Qirf.RuntimeOrdinaryPhis

private def first : Table := [(1,.input 0),(4,.bit true)]
private def second : Table := [(2,.not (.input 0)),(5,.bit false)]
private def phis : List Phi := [⟨1,2,6⟩,⟨4,5,7⟩]

private def operands (left right : Table) (actual : List Phi) :
    Option (List (Nat × Expression × Expression)) :=
  ((readMany left right actual).run 1000000).1.toOption.map fun result =>
    result.map fun pair => (pair.1.output,pair.2.thenValue.expression,pair.2.elseValue.expression)

#guard operands first second phis = some
  [(6,.input 0,.not (.input 0)),(7,.bit true,.bit false)]
#guard operands [] second phis = none
#guard operands first [] phis = none
-- The second phi cannot read the first phi's destination from either arm.
#guard operands first second [⟨1,2,6⟩,⟨6,5,7⟩] = none
#guard operands first second [⟨1,2,6⟩,⟨4,6,7⟩] = none

#print axioms QleisliKernel.Qirf.RuntimeOrdinaryPhis.One.sound
#print axioms QleisliKernel.Qirf.RuntimeOrdinaryPhis.Bound.bothOperands
#print axioms QleisliKernel.Qirf.RuntimeOrdinaryPhis.MergedAt.retains

end QleisliKernel.Tests.RuntimeOrdinaryPhis
