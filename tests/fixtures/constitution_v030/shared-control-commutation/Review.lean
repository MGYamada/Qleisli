import Qleisli.SharedControlCommutation

/-! Closed types and axiom dependencies for the second bounded #303 unit.
No constitutional guarantee or borrow contract is admitted by this review.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
set_option pp.universes true
set_option pp.fullNames true

#check @Qleisli.SharedControlCommutation.block_tensor_commute
#check @Qleisli.SharedControlCommutation.controlled_tensor_commute
#check @Qleisli.SharedControlCommutation.apply_controlled_tensor_commute
#check @Qleisli.SharedControlCommutation.apply_sequence_adjacent_swap
#check @Qleisli.SharedControlCommutation.apply_sequence_adjacent_swap_reference
#print axioms Qleisli.SharedControlCommutation.block_tensor_commute
#print axioms Qleisli.SharedControlCommutation.controlled_tensor_commute
#print axioms Qleisli.SharedControlCommutation.apply_controlled_tensor_commute
#print axioms Qleisli.SharedControlCommutation.apply_sequence_adjacent_swap
#print axioms Qleisli.SharedControlCommutation.apply_sequence_adjacent_swap_reference
