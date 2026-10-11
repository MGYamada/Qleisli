import Qleisli.Semantics.RawLegacy.Observation
import QleisliKernel.Semantics.ClassicalScope

/-! Pre-Unit-opcode semantic fragment for checked representation transport.
Extracted from `lean-kernel/QleisliKernel/Semantics/ClassicalScope.lean` at `bb28608599e5df86b485ad5ff369e22d97a51ae6`
(SHA-256 `de9f6e8ef3bbc8f949ff435243ff1029af6715e3b997e53e9ae216b2435a07d0`). Only imports, namespaces and
references to shared unchanged definitions differ. There is no checker here.
Stable payloads/states/rules are shared; their historical identity must still be checked.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawLegacy.ClassicalScope
open QleisliKernel.Semantics.Observation QleisliKernel.Semantics.ClassicalScope
open Observation

mutual
  inductive Step : State → Observation.Op → State → Prop
    | pure (state op) : Step state (.pure op) state
    | measure (before input output after) (fresh : Insert before output after) :
        Step before (.measure input output) after
    | reset (state input output wire) : Step state (.reset input output wire) state
    | discard (state input) : Step state (.discard input) state
    | constant (before value output after) (fresh : Insert before output after) :
        Step before (.constant value output) after
    | not (before input output after) (access : Visible before input)
        (fresh : Insert before output after) : Step before (.not input output) after
    | xor (before left right output after) (a : Visible before left) (b : Visible before right)
        (fresh : Insert before output after) : Step before (.xor left right output) after
    | and (before left right output after) (a : Visible before left) (b : Visible before right)
        (fresh : Insert before output after) : Step before (.and left right output) after
    | branch (before condition thenOps elseOps quantum classical left right after)
        (access : Visible before condition)
        (thenArm : Run (enter before) thenOps left)
        (elseArm : Run (enter (leave before.current before.next left)) elseOps right)
        (operands : Phis (leave before.current (leave before.current before.next left).next right)
          before.next (leave before.current before.next left).next classical)
        (destinations : Inserts (leave before.current (leave before.current before.next left).next right)
          (classical.map ClassicalPhi.output) after) :
        Step before (.branch condition thenOps elseOps quantum classical) after
  inductive Run : State → List Observation.Op → State → Prop
    | nil (state) : Run state [] state
    | cons (before op middle ops after) (head : Step before op middle)
        (tail : Run middle ops after) : Run before (op :: ops) after
end

/-- Ordinary input, every use/definition in both branches, and every returned
classical value obey lexical SSA. This is independent of quantum ownership,
effect denotation, numerical execution and any optional algorithm request. -/
def ScopeSafe (program : Observation.Program) : Prop :=
  ∃ initial final, Inserts {} program.classicalInputs initial ∧
    Run initial program.operations final ∧ ∀ value ∈ program.classicalOutputs, Visible final value


end Qleisli.Semantics.RawLegacy.ClassicalScope
