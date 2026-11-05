import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.Qirf.RuntimeForestFactorization

/-! Semantic child layouts at the actual original pair-front boundary.
The existing finitePrefixSpan alias is definitionally the original parser.
Its exact successful runs, not a caller-chosen concatenation, determine both
children. This is semantic layout evidence, not bounded reader availability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimePairBasesLayout
open QleisliKernel QleisliKernel.SourceTypes
open Semantics.FiniteCarrier
open SourceRuntimeValues (finitePrefixSpan pairBases)

private theorem step_prefix (atom : Atom) (pending : Nat) (front suffix output : List Layout)
    (count : front.length = pending + (children atom).getD 0)
    (read : layoutStep atom (some (front ++ suffix)) = some output) :
    ∃ combined, layoutStep atom (some front) = some combined ∧
      combined.length = pending+1 ∧ output = combined ++ suffix := by
  cases arities : children atom with
  | none =>
    cases leaves : leaf atom with
    | none => simp [layoutStep,arities,leaves] at read
    | some code =>
      have same : output = code :: (front ++ suffix) := by
        simpa [layoutStep,arities,leaves] using read.symm
      have length : front.length = pending := by
        simpa only [arities,Option.getD_none,Nat.add_zero] using count
      refine ⟨code :: front,?_,congrArg Nat.succ length,same⟩
      simp [layoutStep,arities,leaves]
  | some arity =>
    have length : front.length = pending+arity := by
      simpa only [arities,Option.getD_some] using count
    have bound : arity ≤ front.length := by omega
    have wholeBound : arity ≤ (front ++ suffix).length := by
      simp only [List.length_append]
      omega
    let combined := (front.take arity).foldl tensor singleton :: front.drop arity
    have here : layoutStep atom (some front) = some combined := by
      simp [layoutStep,arities,combined,Nat.not_lt.mpr bound]
    have whole : layoutStep atom (some (front ++ suffix)) = some (combined ++ suffix) := by
      simp only [layoutStep,arities,bind,Option.bind,if_neg (Nat.not_lt.mpr wholeBound),
        List.take_append_of_le_length bound,List.drop_append_of_le_length bound,combined,List.cons_append]
    refine ⟨combined,here,?_,Option.some.inj (read.symm.trans whole)⟩
    simp only [combined,List.length_cons,List.length_drop,length,Nat.add_sub_cancel]

/-- The actual front scan identifies a complete forest of the requested
number of roots. A successful surrounding interpretation cannot lend it nodes
or layouts from the unconsumed suffix. All reference lists are erased here. -/
theorem span_layout (fuel : Nat) :
    ∀ (pending : Nat) (basis reversed front : Basis) (remaining : Semantics.RuntimeType.Tree),
      finitePrefixSpan fuel pending (basis.map Semantics.RuntimeType.Atom.finite) reversed =
        .ok (front,remaining) →
      ∀ suffix output : List Layout,
        basis.foldr layoutStep (some suffix) = some output →
      ∃ (consumed rest : Basis) (prefixLayouts restLayouts : List Layout),
        front = reversed.reverse ++ consumed ∧ basis = consumed ++ rest ∧
        remaining = rest.map Semantics.RuntimeType.Atom.finite ∧ prefixLayouts.length = pending ∧
        consumed.foldr layoutStep (some []) = some prefixLayouts ∧
        rest.foldr layoutStep (some suffix) = some restLayouts ∧ output = prefixLayouts ++ restLayouts := by
  induction fuel with
  | zero =>
    intro pending basis reversed front remaining read suffix output _original
    cases read
  | succ fuel ih =>
    intro pending basis reversed front remaining read suffix output original
    cases pending with
    | zero =>
      change (Except.ok (reversed.reverse,basis.map Semantics.RuntimeType.Atom.finite) :
        Except String (Basis × Semantics.RuntimeType.Tree)) = .ok (front,remaining) at read
      have same := Prod.mk.inj (Except.ok.inj read)
      refine ⟨[],basis,[],output,?_,rfl,same.2.symm,rfl,rfl,original,rfl⟩
      simpa only [List.append_nil] using same.1.symm
    | succ pending =>
      cases basis with
      | nil => cases read
      | cons atom basis =>
        change finitePrefixSpan fuel (pending + (children atom).getD 0)
          (basis.map Semantics.RuntimeType.Atom.finite) (atom :: reversed) = .ok (front,remaining) at read
        cases tail : basis.foldr layoutStep (some suffix) with
        | none =>
          simp [List.foldr_cons,tail,layoutStep] at original
        | some middle =>
          have head : layoutStep atom (some middle) = some output := by
            simpa only [List.foldr_cons,tail] using original
          obtain ⟨consumed,rest,prefixLayouts,restLayouts,prefixEq,basisEq,remainingEq,
            count,prefixRead,restRead,middleEq⟩ :=
              ih (pending + (children atom).getD 0) basis (atom :: reversed) front remaining read
                suffix middle tail
          rw [middleEq] at head
          obtain ⟨combined,combinedRead,combinedCount,outputEq⟩ :=
            step_prefix atom pending prefixLayouts restLayouts output count head
          refine ⟨atom :: consumed,rest,combined,restLayouts,?_,congrArg (List.cons atom) basisEq,
            remainingEq,combinedCount,?_,restRead,outputEq⟩
          · simpa [List.reverse_cons,List.append_assoc] using prefixEq
          · simpa only [List.foldr_cons,prefixRead] using combinedRead

private theorem string_bind_success {α β : Type} (first : Except String α)
    (next : α → Except String β) (value : β) (read : (first >>= next) = .ok value) :
    ∃ selected, first = .ok selected ∧ next selected = .ok value := by
  cases first with
  | error error => cases read
  | ok selected => exact ⟨selected,rfl,read⟩

private theorem singleton_layout (basis : Basis) (code : Layout)
    (read : basis.foldr layoutStep (some []) = some [code]) :
    Semantics.FiniteCarrier.layout basis = some code := by
  unfold Semantics.FiniteCarrier.layout
  exact congrArg (fun (stack : Option (List Layout)) => (do
    let [result] ← stack | none
    pure result)) read

/-- The same successful original pair parser fixes both complete child
layouts. Parent interpretation plus flattened concatenation alone would not
establish this property. No child bounded-reader invocation is inferred. -/
theorem pairBases_layout (basis left right : Basis) (parent : Layout)
    (parsed : pairBases basis = .ok (left,right))
    (original : Semantics.FiniteCarrier.layout basis = some parent) :
    ∃ l r, Semantics.FiniteCarrier.layout left = some l ∧
      Semantics.FiniteCarrier.layout right = some r ∧ parent = tensor l r := by
  cases basis with
  | nil => cases parsed
  | cons atom fields =>
    cases atom with
    | unit => cases parsed
    | bit => cases parsed
    | bits width => cases parsed
    | tuple arity => cases parsed
    | enumeration origin variants => cases parsed
    | record origin fields => cases parsed
    | pair =>
      let tree := fields.map Semantics.RuntimeType.Atom.finite
      change ((do
        let (first,remaining) ← finitePrefixSpan (tree.length+1) 1 tree []
        let (second,remaining) ← finitePrefixSpan (remaining.length+1) 1 remaining []
        if !remaining.isEmpty then throw "source pair basis has trailing fields"
        return (first,second)) : Except String (Basis × Basis)) = .ok (left,right) at parsed
      obtain ⟨⟨first,remaining⟩,firstRead,tail⟩ := string_bind_success _ _ _ parsed
      obtain ⟨⟨second,finalRest⟩,secondRead,returned⟩ := string_bind_success _ _ _ tail
      cases finalRest with
      | cons firstRest rest => cases returned
      | nil =>
        obtain ⟨firstEq,secondEq⟩ := Prod.mk.inj (Except.ok.inj returned)
        subst first
        subst second
        have fieldsRead : ∃ stack, fields.foldr layoutStep (some []) = some stack := by
          cases folded : fields.foldr layoutStep (some []) with
          | none => simp [Semantics.FiniteCarrier.layout,List.foldr_cons,folded,layoutStep] at original
          | some stack => exact ⟨stack,rfl⟩
        obtain ⟨stack,stackRead⟩ := fieldsRead
        obtain ⟨consumed,rest,firstLayouts,restLayouts,prefixEq,fieldsEq,remainingEq,
          firstCount,firstOriginal,restOriginal,_stackEq⟩ :=
            span_layout (tree.length+1) 1 fields [] left remaining firstRead [] stack stackRead
        have consumedEq : left = consumed := by
          simpa only [List.reverse_nil,List.nil_append] using prefixEq
        subst consumed
        have secondRead' : finitePrefixSpan (remaining.length+1) 1
            (rest.map Semantics.RuntimeType.Atom.finite) [] = .ok (right,[]) := by
          rw [← remainingEq]
          exact secondRead
        obtain ⟨consumed,finalBasis,secondLayouts,finalLayouts,prefixEq,restEq,remainingEq,
          secondCount,secondOriginal,_finalOriginal,_restStackEq⟩ :=
            span_layout (remaining.length+1) 1 rest [] right [] secondRead' [] restLayouts restOriginal
        have consumedEq : right = consumed := by
          simpa only [List.reverse_nil,List.nil_append] using prefixEq
        subst consumed
        have finalEmpty : finalBasis = [] := by
          have length := congrArg List.length remainingEq
          exact List.eq_nil_of_length_eq_zero (by
            simpa only [List.length_nil,List.length_map] using length.symm)
        rw [finalEmpty,List.append_nil] at restEq
        obtain ⟨l,leftStack⟩ := List.length_eq_one_iff.mp firstCount
        obtain ⟨r,rightStack⟩ := List.length_eq_one_iff.mp secondCount
        have leftFold : left.foldr layoutStep (some []) = some [l] :=
          firstOriginal.trans (congrArg some leftStack)
        have rightFold : right.foldr layoutStep (some []) = some [r] :=
          secondOriginal.trans (congrArg some rightStack)
        have leftLayout := singleton_layout left l leftFold
        have rightLayout := singleton_layout right r rightFold
        have fieldsPair : fields = left ++ right := fieldsEq.trans (congrArg (List.append left) restEq)
        have parentRead : Semantics.FiniteCarrier.layout (.pair :: (left ++ right)) = some parent := by
          simpa only [fieldsPair] using original
        have pairRead := QleisliKernel.Qirf.RuntimeForestCode.layout_pair_reference
          left right l r leftLayout rightLayout
        exact ⟨l,r,leftLayout,rightLayout,Option.some.inj (parentRead.symm.trans pairRead)⟩

#print axioms span_layout
#print axioms pairBases_layout

end Qleisli.RuntimePairBasesLayout
