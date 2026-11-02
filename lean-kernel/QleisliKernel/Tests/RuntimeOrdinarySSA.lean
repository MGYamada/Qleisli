import QleisliKernel.Qirf.RuntimeOrdinarySSA

/-! Small literal SSA regressions. No quantum instance or native dispatcher is
created here; complete source/storage/history integration remains separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinarySSA
open QleisliKernel QleisliKernel.Qirf.RuntimeOrdinarySSA

private def compiled (operations : List Instruction) (inputs : Table := []) : Option Table :=
  ((readOps operations inputs).run 1000000).1.toOption.map Sigma.fst

#guard compiled [.constant true 1,.not 1 2,.xor 1 2 3,.and 1 3 4] = some
  [(1,.bit true),(2,.not (.bit true)),(3,.xor (.bit true) (.not (.bit true))),
    (4,.and (.bit true) (.xor (.bit true) (.not (.bit true))))]
#guard compiled [.xor 0 0 1] [(0,.input 0)] = some [(0,.input 0),(1,.xor (.input 0) (.input 0))]
#guard compiled [.not 9 1] = none
#guard compiled [.constant false 1,.constant true 1] = none
#guard compiled [.measure 0 1] = none
#guard compiled [.discard 0] = none
#guard compiled [.reset 0 1 2] = none
#guard compiled [.branch 0 [] [] [] []] = none
#guard compiled [.pure (.packUnit 0)] = none

#print axioms QleisliKernel.Qirf.RuntimeOrdinarySSA.Definition.sound
#print axioms QleisliKernel.Qirf.RuntimeOrdinarySSA.Action.preserves
#print axioms QleisliKernel.Qirf.RuntimeOrdinarySSA.Gap.classical

end QleisliKernel.Tests.RuntimeOrdinarySSA
