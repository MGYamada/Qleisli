import Std

/-! Untrusted graph indices for one original provider-body occurrence.
Distinct source ports never become an endomorphic evidence subject by width.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceProviderSubject

inductive Subject where
  | function (evidence : Nat)
  | pure (program : Nat)
  deriving BEq, DecidableEq, Repr

end QleisliKernel.Qirf.SourceProviderSubject
