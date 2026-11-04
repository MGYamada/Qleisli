import QleisliKernel.SourceTypes.GenericOperationSubstitute
import QleisliKernel.FiniteRestriction.Check

/-! Ordered child and parameter correspondence for an actual substituted provider.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperationSubstitute
open Finite GenericOperation Semantics.SymbolicBasis Semantics.SourceAffine

private theorem namedReads {α β : Type} (f : α → WorkM β) (p : α → β → Prop)
    (preserve : ∀ a b start stop, (f a).run start = (.ok b,stop) → p a b)
    (inputs : List (String × α)) (outputs : List (String × β)) {before after : Nat}
    (ran : (inputs.mapM fun (input : String × α) => do
      let (name,a) := input
      let b ← f a
      pure (name,b)).run before = (.ok outputs,after)) :
    Exact.ListRel (fun a b => b.1 = a.1 ∧ p a.2 b.2) inputs outputs := by
  refine FiniteRestriction.mapM_relation _ _ ?_ inputs outputs before after ran
  rintro ⟨name,a⟩ out start stop success
  obtain ⟨b,middle,read,returned⟩ := bind_success _ _ _ _ _ success
  have same : out = (name,b) := (pure_success _ _ _ _ returned).1
  subst out
  exact ⟨rfl,preserve a b start middle read⟩

/-- Reindex each complete supplier list by the sizes of the preceding child
graphs. Entries at the same index and repeated argument occurrences are retained. -/
def providerSuppliers {sources} (children : List (String × Subject sources)) : List (Nat × Origin sources) :=
  (children.foldl (fun (offset,suppliers) (_,value) =>
    (offset+value.description.nodes.length,
      suppliers ++ value.suppliers.map (fun (index,origin) => (index+offset,origin))))
    (0,[])).2

structure ProviderChildren {sources application original} (checked : @Checked sources application original)
    (parent : Step application original) (owner name : String)
    (bases : List (String × Code)) (naturals : List (String × Form))
    (operations : List (String × Nat)) (premises : List (String × OperationPaths.Paths))
    (basisRows : List (String × BasisStep application)) (naturalRows : List (String × NaturalStep application))
    (supplied : List (String × Subject sources)) : Prop where
  basesRead : Exact.ListRel (fun a b => b.1 = a.1 ∧ b.2.original = a.2) bases basisRows
  naturalsRead : Exact.ListRel (fun a b => b.1 = a.1 ∧ b.2.original = a.2) naturals naturalRows
  operationsRead : Exact.ListRel (fun a b => b.1 = a.1 ∧
    ∃ child, UsedChild checked parent a.2 child ∧ child.result.subject = b.2) operations supplied
  retainedBases : parent.result.bases = basisRows.map (·.2)
  retainedNaturals : parent.result.naturals = naturalRows.map (·.2)
  description : parent.result.subject.description = GenericOperation.provider (callerFrame application) owner name
    (basisRows.map fun (key,row) => (key,row.checked.code)) (naturalRows.map fun (key,row) => (key,row.checked.form))
    (supplied.map fun (key,value) => (key,value.description)) premises
  suppliers : parent.result.subject.suppliers =
    providerSuppliers supplied ++ roots original parent.index parent.result.subject.description.root

theorem Checked.provider_children {sources application original} (checked : @Checked sources application original)
    {i : Nat} {parent : Step application original} {owner name bases naturals operations premises}
    (parentAt : checked.result.steps[i]? = some parent)
    (source : parent.node = .provider owner name bases naturals operations premises) :
    ∃ basisRows naturalRows supplied,
      ProviderChildren checked parent owner name bases naturals operations premises basisRows naturalRows supplied := by
  obtain ⟨_,_,ran⟩ := parent.computed
  rw [source] at ran
  unfold readNode at ran
  obtain ⟨_,_,_,afterCharge⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨basisRows,_,mappedBases,afterBases⟩ := bind_success _ _ _ _ _ afterCharge
  obtain ⟨naturalRows,_,mappedNaturals,afterNaturals⟩ := bind_success _ _ _ _ _ afterBases
  obtain ⟨supplied,_,mappedOps,afterOps⟩ := bind_success _ _ _ _ _ afterNaturals
  obtain ⟨_,_,_,returned⟩ := bind_success _ _ _ _ _ afterOps
  have output := (pure_success _ _ _ _ returned).1
  refine ⟨basisRows,naturalRows,supplied,?_,?_,?_,congrArg NodeResult.bases output,
    congrArg NodeResult.naturals output,congrArg (fun r => r.subject.description) output,by rw [output] <;> rfl⟩
  · refine namedReads (basis application) (fun code row => row.original = code) ?_ _ _ mappedBases
    intro code row _ _ read
    unfold basis at read
    obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ read
    have same := (pure_success _ _ _ _ tail).1
    exact congrArg BasisStep.original same
  · refine namedReads (natural application) (fun form row => row.original = form) ?_ _ _ mappedNaturals
    intro form row _ _ read
    unfold natural at read
    obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ read
    have same := (pure_success _ _ _ _ tail).1
    exact congrArg NaturalStep.original same
  · exact namedReads (fun j => lift (readOption parent.previous[j]?))
      (fun j value => ∃ child, UsedChild checked parent j child ∧ child.result.subject = value)
      (fun _ _ _ _ read => checked.child_at parentAt (readOption_selected read)) _ _ mappedOps

/-- An Op-argument position in this particular provider selects a checked
original child and the supplied subject at exactly that position. -/
theorem ProviderChildren.operation_at {sources application original checked parent owner name bases naturals operations
    premises basisRows naturalRows supplied}
    (children : @ProviderChildren sources application original checked parent owner name bases naturals operations
      premises basisRows naturalRows supplied)
    {position index : Nat} {argumentName : String} (selected : operations[position]? = some (argumentName,index)) :
    ∃ child, supplied[position]? = some (argumentName,child.result.subject) ∧ UsedChild checked parent index child := by
  obtain ⟨bound,originalAt⟩ := List.getElem?_eq_some_iff.mp selected
  have inside : position < supplied.length := by
    rw [Exact.listRel_length _ _ _ children.operationsRead]
    exact bound
  have related := Exact.listRel_getElem _ _ _ children.operationsRead position bound
  rw [originalAt] at related
  obtain ⟨same,child,used,value⟩ := related
  have actual : supplied[position]'inside = (argumentName,child.result.subject) := Prod.ext same value.symm
  exact ⟨child,(List.getElem?_eq_getElem inside).trans (congrArg some actual),used⟩

end QleisliKernel.SourceTypes.GenericOperationSubstitute
