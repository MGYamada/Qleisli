import QleisliKernel.Tests.SectorArms.Data

/-! Small original-arm/control regression stages. Exact original definitions
and theorem bodies are retained in separately compiled modules to bound kernel
reduction memory. No proof/native policy or semantic oracle is weakened.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SectorArms
open Semantics.Exact Semantics.Finite Semantics.CarrierInterface
open QleisliKernel.Tests.FiniteRestriction

theorem actual_subject_roots : Qirf.SectorArms.subjectRoots 0 references = [0,3,4,1,2] := by
  decide +kernel

theorem subject_reuse_is_deduplicated : Qirf.SectorArms.subjectRoots 9
    [zeroRef,{zeroRef with label := 1}] = [9,0,1] := by decide +kernel

private theorem graph_reachable (data : Qirf.Artifact) (order : Array Nat)
    (extra : List (String × String)) (roots : List Nat) (dependencies : List Dependency) (work left : Nat)
    (ok : (Qirf.checkGraphFromRoots data order extra roots).run work = (.ok dependencies,left)) :
    Hierarchical.Graph.reachable (Qirf.nodes data) order roots = true := by
  obtain ⟨receipts,middle,checked,_⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨schedule,selected,_⟩ := Qirf.checkGraphReceiptsFromRoots_schedule _ _ _ _ _ _ _ checked
  exact (Hierarchical.Graph.check_conditions _ _ _ _ selected).2.2.2.1

theorem ordinary_reachability_stays_strict :
    Hierarchical.Graph.reachable (Qirf.nodes whole) #[1,2,3,4,0] [0] = false := by decide +kernel

theorem ordinary_root_still_refuses (work : Nat) :
    ((Qirf.Validity.checkRoot whole #[1,2,3,4,0]).run work).1.isOk = false := by
  cases outcome : (Qirf.Validity.checkRoot whole #[1,2,3,4,0]).run work with
  | mk result left =>
    cases result with
    | error error => rfl
    | ok checked =>
      have facts := Qirf.Validity.checkRoot_postcondition _ _ _ _ _ outcome
      obtain ⟨after,graph⟩ := facts.graph
      have reachable := graph_reachable whole #[1,2,3,4,0] [] [0] checked.dependencies work after graph
      rw [ordinary_reachability_stays_strict] at reachable
      cases reachable

theorem unrelated_node_is_not_a_subject : Hierarchical.Graph.reachable (Qirf.nodes unrelated)
    #[1,2,3,4,5,0] (Qirf.SectorArms.subjectRoots unrelated.root references) = false := by decide +kernel

theorem unrelated_node_refuses (work : Nat) :
    ((Qirf.SectorArms.check unrelated #[1,2,3,4,5,0] interface interface references).run work).1.isOk = false := by
  cases outcome : (Qirf.SectorArms.check unrelated #[1,2,3,4,5,0] interface interface references).run work with
  | mk result left =>
    cases result with
    | error error => rfl
    | ok checked =>
      have facts := Qirf.SectorArms.check_bound _ _ _ _ _ _ _ _ outcome
      obtain ⟨rootWork,rootFacts⟩ := facts.subject.root
      obtain ⟨after,graph⟩ := rootFacts.graph
      have reachable := graph_reachable _ _ _ _ _ _ _ graph
      rw [facts.roots,unrelated_node_is_not_a_subject] at reachable
      cases reachable

theorem subject_roots_do_not_supply_source_usage (work : Nat) :
    ((Qirf.SectorArms.check unusedSource #[1,2,3,4,0] interface interface references).run work).1.isOk = false := by
  cases outcome : (Qirf.SectorArms.check unusedSource #[1,2,3,4,0] interface interface references).run work with
  | mk result left =>
    cases result with
    | error error => rfl
    | ok checked =>
      have facts := Qirf.SectorArms.check_bound _ _ _ _ _ _ _ _ outcome
      obtain ⟨_,rootFacts⟩ := facts.subject.root
      have refuses : Qirf.Validity.sourcesUsedWithSources unusedSource
          (Qirf.Carrier.sourceRows interface interface) = false := by decide +kernel
      have impossible : (true : Bool) = false := rootFacts.sources.symm.trans refuses
      cases impossible

end QleisliKernel.Tests.SectorArms
