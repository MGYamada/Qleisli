import Qleisli.Semantics.Raw
import QleisliKernel.Raw.Unit

/-! Exact event-meaning laws for the executable zero-axis owner building
blocks. The input matrix is arbitrary; existing scalar phase is not replaced
by an identity matrix. Public Raw decoding/dispatch and original-program
preservation are still separate integration obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RawUnit
open QleisliKernel QleisliKernel.Semantics.Exact

theorem pack_events_preserve (state : Raw.State) (output : Nat) (result : Raw.Transition)
    (dependencies : List QleisliKernel.Semantics.Finite.Dependency) (input : Matrix)
    (ok : Raw.Unit.pack state output = .ok result) :
    Qleisli.Semantics.Raw.EventsMeaning dependencies result.events input input := by
  rw [(Raw.Unit.pack_conditions _ _ _ ok).2.2.2]
  exact .nil input

theorem unpack_events_preserve (state : Raw.State) (inputToken : Nat) (result : Raw.Transition)
    (dependencies : List QleisliKernel.Semantics.Finite.Dependency) (input : Matrix)
    (ok : Raw.Unit.unpack state inputToken = .ok result) :
    Qleisli.Semantics.Raw.EventsMeaning dependencies result.events input input := by
  obtain ⟨_,_,_,_,_,_,events⟩ := Raw.Unit.unpack_conditions _ _ _ ok
  rw [events]
  exact .nil input

end Qleisli.RawUnit
