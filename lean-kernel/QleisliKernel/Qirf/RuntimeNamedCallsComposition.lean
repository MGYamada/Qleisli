import QleisliKernel.Qirf.RuntimeNamedCalls
import QleisliKernel.Qirf.RuntimePureComposition

/-! Literal composition for the authentic ordered caller. Source order,
effects, local equations and complete owner histories come from the retained
call walk. The shared partition binds its nodes to the same original Raw root,
including the real final permutation. This supplies no global typed-code or
source-operator theorem and issues no accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedCallsComposition
open QleisliKernel Finite SourceTypes

abbrev Checked {artifact owner name arguments source request prepared root runtime}
    (calls : @RuntimeNamedCalls.AtRoot artifact owner name arguments source request prepared root runtime) :=
  RuntimePureComposition.Original root calls.native.block calls.result.nodes

def read {artifact owner name arguments source request prepared root runtime}
    (calls : @RuntimeNamedCalls.AtRoot artifact owner name arguments source request prepared root runtime) :
    WorkM (Checked calls) :=
  RuntimePureComposition.readOriginal root calls.result.nodes

end QleisliKernel.Qirf.RuntimeNamedCallsComposition
