import Qleisli.Semantics.OrdinaryValue

/-! Examples of the actual simultaneous Raw phi evaluation order.
These do not establish a typed output tree or full program replay.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.OrdinaryValue.Examples

theorem simultaneous_swap :
    phiBindings true [⟨1,9,3⟩,⟨0,8,4⟩] [(0,false),(1,true)] =
      some [(3,true),(4,false)] := rfl

/-- Output 3 is not available to the next phi; both read incoming bindings. -/
theorem cannot_chain_phi_destinations :
    phiBindings true [⟨1,9,3⟩,⟨3,8,4⟩] [(0,false),(1,true)] = none := rfl

theorem wrong_arm_selects_different_values :
    phiBindings false [⟨0,1,3⟩] [(0,false),(1,true)] = some [(3,true)] := rfl

end Qleisli.Semantics.OrdinaryValue.Examples
