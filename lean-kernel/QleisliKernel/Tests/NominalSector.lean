import QleisliKernel.Qirf.NominalSector
import QleisliKernel.Tests.FiniteRestriction

/-! Small independent code/matrix/policy oracles, three physical bits at most.
Generic check_bound composes these stages with original source/QIRF/Raw checks;
do not kernel-reduce the complete repeated parser/graph pipeline in each case.
No limits are raised and no native proof evaluation is used.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.NominalSector
open Semantics.Exact Semantics.CarrierInterface Qirf.NominalSector
open QleisliKernel.Tests.FiniteRestriction

def tri : Semantics.FiniteCarrier.Basis :=
  [.enumeration ⟨"labels","Tri","pub enum Tri { A, B, C }"⟩ ["A","B","C"]]
def code : Matrix := Semantics.FiniteCarrier.encoding ⟨2,[0,1,2]⟩
def cycle3 : Matrix := ⟨3,3,[0,0,1,1,0,0,0,1,0].map fun n =>
  ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
def identity3 : Matrix := ⟨3,3,[1,0,0,0,1,0,0,0,1].map fun n =>
  ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
def cycle4 : Matrix := ⟨4,4,[
  0,0,1,0, 1,0,0,0, 0,1,0,0, 0,0,0,1].map fun n =>
  ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
def leakage4 : Matrix := ⟨4,4,[
  1,0,0,0, 0,1,0,0, 0,0,0,1, 0,0,1,0].map fun n =>
  ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
def zero3 : Matrix := ⟨3,3,List.replicate 9 Scalar.zero⟩

def outcome (inputCode outputCode : Matrix) (physical : List Matrix) (label : Nat)
    (meaning : Matrix) : Except Finite.Error (List Matrix) :=
  ((checkLogical inputCode outputCode physical (label,meaning)).run 1000000).1.map fun value => [value]

theorem fresh_three_state_code :
    (((FiniteCarrier.code tri).run 1000000).1.map (fun value => [value]) == .ok [code]) = true := by
  decide +kernel

theorem exact_three_cycle : (outcome code code [cycle4] 0 cycle3 == .ok [cycle3]) = true := by
  decide +kernel

theorem actual_body_is_bound : (outcome code code [cycle4] 0 identity3 == .error .equation) = true := by
  decide +kernel

theorem physical_padding_cannot_leak : (outcome code code [leakage4] 0 identity3 == .error .equation) = true := by
  decide +kernel

theorem logical_dimension_is_three : (outcome code code [identity4] 0 identity4 == .error .request) = true := by
  decide +kernel

theorem nonunitary_logical_map_refuses : (outcome code code [identity4] 0 zero3 == .error .notIsometric) = true := by
  decide +kernel

theorem missing_physical_sector_refuses : (outcome code code [] 0 identity3 == .error .invalid) = true := by
  decide +kernel

theorem exact_scalar_phase : (outcome (scalar Scalar.one) (scalar Scalar.one)
    [scalar negativeOne] 0 (scalar Scalar.one) == .error .equation) = true := by decide +kernel

def selector : Semantics.FiniteCarrier.Basis := .pair :: tri ++ [.bit]
def physical : List Matrix := [scalar Scalar.one,scalar negativeOne,scalar imaginaryOne,
  scalar Scalar.one,scalar negativeImaginary,scalar negativeOne,scalar Scalar.one,scalar imaginaryOne]
def logical : List Matrix := [scalar Scalar.one,scalar negativeOne,scalar imaginaryOne,
  scalar negativeImaginary,scalar negativeOne,scalar Scalar.one]

theorem noncontiguous_product_labels : Semantics.FiniteCarrier.layout selector =
    some ⟨3,[0,1,2,4,5,6]⟩ := by decide +kernel

theorem logical_label_order : (((checkLogicals (scalar Scalar.one) (scalar Scalar.one)
    physical [0,1,2,4,5,6] logical).run 1000000).1 == .ok logical) = true := by decide +kernel

theorem logical_label_substitution_refuses : (((checkLogicals (scalar Scalar.one) (scalar Scalar.one)
    physical [0,1,2,3,4,5] logical).run 1000000).1 == .error .equation) = true := by decide +kernel

theorem physical_width_is_not_cardinality : (((checkLogicals (scalar Scalar.one) (scalar Scalar.one)
    fourMeanings [0,1,2] fourMeanings).run 1000000).1 == .error .request) = true := by decide +kernel

def quad : Semantics.FiniteCarrier.Basis :=
  [.enumeration ⟨"labels","Quad","pub enum Quad { A, B, C, D }"⟩ ["A","B","C","D"]]
def p : Ports := ⟨⟨⟨10,[],0⟩,[.unit]⟩,⟨⟨11,[7,91],2⟩,tri⟩,
  ⟨⟨14,[],0⟩,[.unit]⟩,⟨⟨15,[7,91],2⟩,quad⟩⟩
def interface : Interface := ⟨[p.selectorIn,p.targetIn],[p.selectorOut,p.targetOut],.unitary⟩

theorem equal_width_nominal_substitution_refuses : sameTypes interface p = false := by decide +kernel

theorem public_isometry_does_not_grant_unitary : sameTypes {interface with publicEffect := .iso}
    {p with targetOut := p.targetIn} = false := by decide +kernel

theorem zero_width_nominal_shape_is_retained : sameTypes interface
    {p with selectorOut := ⟨p.selectorOut.port,[.bits 0]⟩,targetOut := p.targetIn} = false := by
  decide +kernel

end QleisliKernel.Tests.NominalSector
