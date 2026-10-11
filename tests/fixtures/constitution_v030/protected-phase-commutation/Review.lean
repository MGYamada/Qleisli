import Qleisli.RawProtectedCommutation

/-! Closed types and actual axiom dependencies for the first issue #303 unit.
This review does not admit a constitutional guarantee or a borrow contract.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
set_option pp.universes true
set_option pp.fullNames true

#check @Qleisli.Raw.ProtectedCommutation.phase_use_commute
#check @Qleisli.Raw.ProtectedCommutation.run_adjacent_phase_swap
#check @Qleisli.Raw.ProtectedCommutation.coefficient_adjacent_phase_swap
#check @Qleisli.Raw.ProtectedCommutation.checked_matrix_phase_swap
#check @Qleisli.Raw.ProtectedCommutation.checked_matrix_phase_swap_action

#print axioms Qleisli.Raw.ProtectedCommutation.phase_use_commute
#print axioms Qleisli.Raw.ProtectedCommutation.run_adjacent_phase_swap
#print axioms Qleisli.Raw.ProtectedCommutation.coefficient_adjacent_phase_swap
#print axioms Qleisli.Raw.ProtectedCommutation.checked_matrix_phase_swap
#print axioms Qleisli.Raw.ProtectedCommutation.checked_matrix_phase_swap_action
