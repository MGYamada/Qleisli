import QleisliKernel.Qirf.RuntimeArmDutyCoverage

/-! Reconcile the complete original Meaning queue after the native body
traversal. Keep the initial assessments and each unresolved original position.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyOperations
open QleisliKernel Finite SourceTypes

structure Checked {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) (order : Array Nat) (runtime : RuntimeFamily.Request)
    extends Traversed prepared order runtime where
  traversed : RuntimeInterval.Computed (traverse prepared order runtime) toTraversed
  coverage : RuntimeArmDutyCoverage.Report toTraversed (List.finRange prepared.source.pending.entries.length)
  reconciled : RuntimeInterval.Computed (RuntimeArmDutyCoverage.read toTraversed) coverage

def read {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) (order : Array Nat) (runtime : RuntimeFamily.Request) :
    WorkM (Checked prepared order runtime) := do
  let body ← NaturalAffine.witness (traverse prepared order runtime)
  let coverage ← NaturalAffine.witness (RuntimeArmDutyCoverage.read body.val)
  return ⟨body.val,by with_reducible exact body.property,coverage.val,by with_reducible exact coverage.property⟩

end QleisliKernel.Qirf.RuntimeBodyOperations
