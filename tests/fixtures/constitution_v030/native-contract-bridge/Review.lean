import Qleisli.NativeContract

/-! Review the actual native byte-entry theorem and the leaf interpretation.
These declarations are ordinary QS proof work, not a guarantee admission.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

set_option pp.universes true

#check @QleisliKernel.Protocol.NativeContract.check_acceptance
#check @Qleisli.NativeContract.acceptance_root_meaning
#check @Qleisli.NativeContract.check_root_meaning
#check @Qleisli.NativeContract.leaf_meaning
#check @Qleisli.NativeContract.leaf_reference_laws
#check @Qleisli.NativeContract.check_sound
#print QleisliKernel.Protocol.NativeContract.Acceptance
#print QleisliKernel.Protocol.NativeContract.EncodedAcceptance
#print QleisliKernel.Protocol.NativeContract.LeafAcceptance
#print QleisliKernel.Protocol.NativeContract.PortBinding
#print Qleisli.NativeContract.LeafMeaning

#print axioms QleisliKernel.Protocol.NativeContract.check_acceptance
#print axioms Qleisli.NativeContract.acceptance_root_meaning
#print axioms Qleisli.NativeContract.check_root_meaning
#print axioms Qleisli.NativeContract.leaf_meaning
#print axioms Qleisli.NativeContract.leaf_reference_laws
#print axioms Qleisli.NativeContract.check_sound
