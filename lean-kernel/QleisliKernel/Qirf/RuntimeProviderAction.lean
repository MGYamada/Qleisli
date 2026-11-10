import QleisliKernel.Qirf.RuntimeProviderPaths
import QleisliKernel.Qirf.RuntimePureBody

/-! Check an original provider body against its demanded paths and exact
native program, under the caller's existing dependency root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeProviderAction
open QleisliKernel Finite SourceTypes

/-- The complete original provider-body run against its verified input
owner. The caller supplies either an existing dense-path port receipt or the
same receipt read before any whole-provider operator reconstruction. -/
structure BodyChecked {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (native : PureProviderSubject.VerifiedPorts header.original.supplied.provider root.dependencies program) where
  initial : RuntimeOwnerMap.Map
  initialRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
    (header.original.body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners)
    [(⟨native.ports.input,native.ports.domain⟩ : Semantics.CarrierInterface.Owner)]) initial
  interval : RuntimeInterval.Prepared root.dependencies program
  intervalRead : RuntimeInterval.Computed (RuntimeInterval.prepare root.dependencies program) interval
  body : RuntimePureBody.Checked artifact root header.original.body program request.2 initial
  consumed : RuntimeInterval.Computed (RuntimePureBody.checkPrepared artifact root header.original.body
    program request.2 initial interval) body

def readBody {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (native : PureProviderSubject.VerifiedPorts header.original.supplied.provider root.dependencies program) :
    WorkM (BodyChecked header root native) := do
  let body := header.original.body
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let owner : Semantics.CarrierInterface.Owner := ⟨native.ports.input,native.ports.domain⟩
  let initial ← NaturalAffine.witness (RuntimeSourceBoundary.bindings roles [owner])
  let interval ← NaturalAffine.witness (RuntimeInterval.prepare root.dependencies program)
  let checked ← NaturalAffine.witness (RuntimePureBody.checkPrepared artifact root body
    program request.2 initial.val interval.val)
  return ⟨initial.val,by with_reducible exact initial.property,
    interval.val,by with_reducible exact interval.property,checked.val,by with_reducible exact checked.property⟩

structure Checked {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (demand : StaticOperation.Paths) where
  paths : RuntimeProviderPaths.Checked header root demand
  pathRead : RuntimeInterval.Computed (RuntimeProviderPaths.read header root demand) paths
  originalBody : BodyChecked header root paths.ir.original.prepared.toVerifiedPorts

def read {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (demand : StaticOperation.Paths) : WorkM (Checked header root demand) := do
  let paths ← NaturalAffine.witness (RuntimeProviderPaths.read header root demand)
  let body ← readBody header root paths.val.ir.original.prepared.toVerifiedPorts
  return ⟨paths.val,by with_reducible exact paths.property,body⟩

def Checked.action {artifact context description graph index request header root demand}
    (checked : @Checked artifact context description graph index request header root demand) : Semantics.Exact.Matrix :=
  checked.paths.ir.original.prepared.equations.action

end QleisliKernel.Qirf.RuntimeProviderAction
