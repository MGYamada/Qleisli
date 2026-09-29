import Qleisli.HierarchicalAcceptance
import QleisliKernel.Hierarchical.CallLowering

/-! Coordinate semantics of shared calls and their existing-node expansion.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The producer is untrusted. These equations preserve the actual ordered maps;
ordinary derivation checking of the generated nodes remains mandatory. -/

namespace Qleisli.CallLowering
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalSemantics HierarchicalUnitary HierarchicalTyping
open scoped Matrix BigOperators

noncomputable def adapters (parent callee : Interface) (input output : PortMap)
    (child : Operator) : List Operator :=
  [apply ⟨parent.inputs,callee.inputs⟩ (.rewire input.axes.toList) [],child,
   apply ⟨callee.outputs,parent.outputs⟩ (.rewire output.axes.toList) []]

noncomputable def expanded (parent callee : Interface) (input output : PortMap)
    (child : Operator) : Operator :=
  apply parent .sequence (adapters parent callee input output child)

theorem typed_unitary (artifact : Artifact) (parent callee : Definition)
    (index : Nat) (input output : PortMap)
    (body : parent.body = .call index input output)
    (found : artifact.definitions[index]? = some callee)
    (typed : NodeTyping.conditions artifact parent = true)
    (child : Operator) (ready : UnitaryInterface callee.interface child) :
    UnitaryInterface parent.interface (expanded parent.interface callee.interface input output child) := by
  obtain ⟨hin,hout,_⟩ := QleisliKernel.Hierarchical.CallLowering.typed_maps
    artifact parent callee index input output body found typed
  have wi := (ports_width _ _ input hin).1
  have wo := (ports_width _ _ output hout).1
  have before := HierarchicalTyping.rewire_unitary ⟨parent.interface.inputs,callee.interface.inputs⟩ input hin
  have after := HierarchicalTyping.rewire_unitary ⟨callee.interface.outputs,parent.interface.outputs⟩ output hout
  apply unitaryInterface_apply
  apply apply_sequence_unitary _ (width parent.interface.inputs) _ rfl
  · exact wo.symm.trans (ready.widths.trans wi.symm)
  · intro operation member
    simp only [adapters,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact before
    · simpa only [wi] using ready.1
    · simpa only [wi,ready.widths] using after

theorem permutation_transport {I : Type} [Fintype I] [DecidableEq I]
    (input output : I ≃ I) (operator : Matrix I I ℂ) :
    permutation output * operator * permutation input =
      operator.submatrix output.symm input := by
  ext row column
  have right (r c : I) : (operator * permutation input) r c = operator r (input c) := by
    simp [Matrix.mul_apply,permutation]
  have select (x : I) : (row = output x) ↔ (x = output.symm row) := by
    constructor
    · intro h; simpa using (congrArg output.symm h).symm
    · intro h; rw [h]; simp
  rw [Matrix.mul_assoc]
  change (∑ x, permutation output row x * (operator * permutation input) x column) = _
  simp only [right,permutation,ite_mul,one_mul,zero_mul,select]
  simp

theorem matrix_rewire (interface : Interface) (n : Nat) (forward backward : List Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (h : QleisliKernel.Layout.Permutation n forward backward) :
    matrixAt n n (apply interface (.rewire forward) []) = permutation (axisEquiv h) := by
  ext output input
  simp only [matrixAt,apply,bounded,raw,hi,ho,List.length_ofFn,and_self,ite_true]
  rw [← axisEquiv_list h]
  simp [permutation,List.ofFn_inj]

theorem matrix_three (n : Nat) (first middle last : Operator)
    (fi : first.inputWidth = n) (fo : first.outputWidth = n)
    (mi : middle.inputWidth = n) (mo : middle.outputWidth = n)
    (li : last.inputWidth = n) (lo : last.outputWidth = n) :
    matrixAt n n (sequence n [first,middle,last]) =
      matrixAt n n last * matrixAt n n middle * matrixAt n n first := by
  have rule (a b : Operator) (ai : a.inputWidth = n) (ao : a.outputWidth = n)
      (bi : b.inputWidth = n) :
      matrixAt n n (compose a b) = matrixAt n n a * matrixAt n n b := by
    have h := HierarchicalOperators.matrix_compose a b
    rw [ai,ao,bi] at h
    exact h
  simp only [HierarchicalOperators.sequence,List.foldl_cons,List.foldl_nil]
  rw [rule last _ li lo (by rfl), rule middle _ mi mo (by rfl),
    rule first _ fi fo rfl, matrix_identity,Matrix.mul_one,Matrix.mul_assoc]

theorem expanded_matrix (parent callee : Interface) (input output : PortMap)
    (child : Operator) (n : Nat)
    (pi : width parent.inputs = n) (po : width parent.outputs = n)
    (ci : width callee.inputs = n) (co : width callee.outputs = n)
    (hi : child.inputWidth = n) (ho : child.outputWidth = n) :
    matrixAt n n (expanded parent callee input output child) =
      matrixAt n n (apply ⟨callee.outputs,parent.outputs⟩ (.rewire output.axes.toList) []) *
      matrixAt n n child *
      matrixAt n n (apply ⟨parent.inputs,callee.inputs⟩ (.rewire input.axes.toList) []) := by
  have same : matrixAt n n (expanded parent callee input output child) =
      matrixAt n n (HierarchicalOperators.sequence n (adapters parent callee input output child)) := by
    ext row column
    simp [matrixAt,expanded,apply,bounded,raw,pi,po]
  rw [same]
  exact matrix_three n _ child _ pi ci hi ho co po

/-- The generated three nodes have the direct call coefficients: relabel the
input by its actual map and pull the output back by the inverse output map.
The two maps need not be equal, self-inverse, or preserve caller port order. -/
theorem typed_coordinates (artifact : Artifact) (parent callee : Definition)
    (index : Nat) (input output : PortMap)
    (body : parent.body = .call index input output)
    (found : artifact.definitions[index]? = some callee)
    (typed : NodeTyping.conditions artifact parent = true)
    (child : Operator) (ready : UnitaryInterface callee.interface child) :
    let n := width callee.interface.inputs
    ∃ inputRoute outputRoute : (Fin n → Bool) ≃ (Fin n → Bool),
      (∀ bits, List.ofFn (inputRoute bits) = input.axes.toList.map
        (fun i => (List.ofFn bits)[i]?.getD false)) ∧
      (∀ bits, List.ofFn (outputRoute bits) = output.axes.toList.map
        (fun i => (List.ofFn bits)[i]?.getD false)) ∧
      matrixAt n n (expanded parent.interface callee.interface input output child) =
        (matrixAt n n child).submatrix outputRoute.symm inputRoute := by
  obtain ⟨hin,hout,_⟩ := QleisliKernel.Hierarchical.CallLowering.typed_maps
    artifact parent callee index input output body found typed
  obtain ⟨wi,ip⟩ := ports_width _ _ input hin
  obtain ⟨wo,op⟩ := ports_width _ _ output hout
  rw [wi] at ip
  rw [ready.widths] at op
  refine ⟨axisEquiv ip,axisEquiv op,axisEquiv_list ip,axisEquiv_list op,?_⟩
  have po := wo.symm.trans ready.widths
  rw [expanded_matrix _ _ input output child _ wi po rfl ready.widths ready.1.1 ready.1.2.1]
  rw [matrix_rewire ⟨callee.interface.outputs,parent.interface.outputs⟩ _ _ _ ready.widths po op,
    matrix_rewire ⟨parent.interface.inputs,callee.interface.inputs⟩ _ _ _ wi rfl ip]
  exact permutation_transport _ _ _

/-- Reference extension is an equation of whole joint-state transformations,
not a statement about isolated basis probabilities or uncorrelated inputs. -/
theorem transport_reference {I R : Type} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] (input output : I ≃ I)
    (operator : Matrix I I ℂ) (rho : Matrix (I × R) (I × R) ℂ) :
    referenceMap (permutation output * operator * permutation input) rho =
      referenceMap (operator.submatrix output.symm input) rho := by
  rw [permutation_transport]

end Qleisli.CallLowering
