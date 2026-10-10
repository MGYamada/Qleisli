import QleisliKernel.Semantics.RawTrace

/-! Structural zero-axis owner maps, independently of acceptance. These are
interface actions with no physical event: the exact coefficient is +1, so no
preceding scalar or external-reference action is erased. These interface maps
describe the packUnit/unpackUnit cases of the independent Raw reader.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.RawUnit
open Raw RawTrace

def pack (state : Interface) (output : Nat) : Interface :=
  RawTrace.insert state output []

def unpack (state : Interface) (input : Nat) : Option Interface := do
  let (port,next) ← RawTrace.take state input
  if port.bits == 0 && port.wires.isEmpty then some next else none

/-- Structural maps do not append a physical action or erase earlier events. -/
def events : List Raw.Event := []

theorem pack_frame (state : Interface) (output : Nat) :
    (pack state output).frame = state.frame := rfl

theorem unpack_frame (state next : Interface) (input : Nat)
    (ok : unpack state input = some next) : next.frame = state.frame := by
  unfold unpack RawTrace.take at ok
  cases found : state.live.find? (fun port => port.token == input) with
  | none => simp [found] at ok
  | some port =>
    simp only [found,bind,Option.bind,pure] at ok
    split at ok
    · cases ok; rfl
    · contradiction

/-- Zero-axis maps preserve every physical state, including phase and arbitrary
reference data. This identity uses no numerical approximation. -/
theorem events_identity {α : Type} (action : α → Raw.Event → α) (state : α) :
    events.foldl action state = state := rfl

end QleisliKernel.Semantics.RawUnit
