import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.Qirf.SourceFrameSector

/-! Neutral selection requests and fresh-root evidence shared by the structural
sequence and general-context checkers. This module grants no acceptance route.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SelectionContract
open Finite Semantics.CarrierInterface
open PureInterval (Witness)
abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  ∃ work left, action.run work = (.ok value,left)

structure Request where
  attached : Interface
  required : Interface
  position : SourceSequence.Position
  programs : List SourceArm.Programs
  deriving BEq, DecidableEq, Repr

theorem rootFresh {artifact order rows roots}
    (root : Witness (Validity.checkRootFromRoots artifact order rows roots)) :
    CheckedGraph artifact (Array.replicate artifact.entries.size none) order.toList root.val.receipts := by
  obtain ⟨work,left,ran⟩ := root.property
  exact (Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ ran).fresh

end QleisliKernel.Qirf.SelectionContract
