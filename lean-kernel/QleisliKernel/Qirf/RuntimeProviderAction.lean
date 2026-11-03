import QleisliKernel.Qirf.RuntimeProviderPaths
import QleisliKernel.Qirf.RuntimePureBody

/-! Check an original provider body against its demanded paths and exact
native program, under the caller's existing dependency root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeProviderAction
open QleisliKernel Finite SourceTypes

structure Checked {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (demand : StaticOperation.Paths) where
  paths : RuntimeProviderPaths.Checked header root demand
  pathRead : RuntimeInterval.Computed (RuntimeProviderPaths.read header root demand) paths
  initial : RuntimeOwnerMap.Map
  initialRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
    (header.original.body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners)
    [(⟨paths.ir.original.prepared.ports.input,paths.ir.original.prepared.ports.domain⟩ :
      Semantics.CarrierInterface.Owner)]) initial
  interval : RuntimeInterval.Prepared root.dependencies paths.ir.original.program
  intervalRead : RuntimeInterval.Computed (RuntimeInterval.prepare root.dependencies paths.ir.original.program) interval
  body : RuntimePureBody.Checked artifact root header.original.body paths.ir.original.program request.2 initial
  consumed : RuntimeInterval.Computed (RuntimePureBody.checkPrepared artifact root header.original.body
    paths.ir.original.program request.2 initial interval) body

def read {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (demand : StaticOperation.Paths) : WorkM (Checked header root demand) := do
  let paths ← NaturalAffine.witness (RuntimeProviderPaths.read header root demand)
  let native := paths.val.ir.original
  let body := header.original.body
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let owner : Semantics.CarrierInterface.Owner := ⟨native.prepared.ports.input,native.prepared.ports.domain⟩
  let initial ← NaturalAffine.witness (RuntimeSourceBoundary.bindings roles [owner])
  let interval ← NaturalAffine.witness (RuntimeInterval.prepare root.dependencies native.program)
  let checked ← NaturalAffine.witness (RuntimePureBody.checkPrepared artifact root body
    native.program request.2 initial.val interval.val)
  return ⟨paths.val,by with_reducible exact paths.property,initial.val,by with_reducible exact initial.property,
    interval.val,by with_reducible exact interval.property,checked.val,by with_reducible exact checked.property⟩

def Checked.action {artifact context description graph index request header root demand}
    (checked : @Checked artifact context description graph index request header root demand) : Semantics.Exact.Matrix :=
  checked.paths.ir.original.prepared.equations.action

end QleisliKernel.Qirf.RuntimeProviderAction
