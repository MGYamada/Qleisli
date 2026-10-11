import Qleisli.NativeValidity

/-! Review material for possible initial scoped QS ledger guarantees.
No declaration is admitted to the ledger merely by checking this file.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs false
set_option format.width 120

-- Actual packet acceptance and the independently defined structural properties.
#check @QleisliKernel.Protocol.Validity.check
#check @QleisliKernel.Protocol.Validity.Acceptance
#check @QleisliKernel.Protocol.Validity.check_acceptance
#check @QleisliKernel.Protocol.Validity.check_ownershipSafe
#check @Qleisli.NativeValidity.check_scopeSafe
#print QleisliKernel.Semantics.Ownership.OwnershipSafe
#print QleisliKernel.Semantics.ClassicalScope.ScopeSafe
#print axioms QleisliKernel.Protocol.Validity.check_acceptance
#print axioms QleisliKernel.Protocol.Validity.check_ownershipSafe
#print axioms Qleisli.NativeValidity.check_scopeSafe
