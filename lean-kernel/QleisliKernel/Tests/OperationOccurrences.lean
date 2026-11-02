import QleisliKernel.SourceTypes.OperationDescription

/-! Small per-edge operation-description occurrence checks. No quantum body or
maximum tree is constructed. The universal bound concerns the actual reader.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.OperationOccurrences
open SourceTypes.OperationDescription

private def leaf : Node := .provider "main" "keep" [] [] []

#guard ((Description.mk [leaf,.thenOp 0 0] 1).treeSize.toOption == some 3)
#guard ((Description.mk [leaf,.thenOp 0 0] 1).occurrences.toOption == some [0,0,1])
#guard ((Description.mk [leaf,.provider "main" "unused" [] [] [("U",0),("V",0)]] 1).occurrences.toOption == some [0,0,1])
#guard ((Description.mk [leaf,.power 0 0] 1).occurrences.toOption == some [0,1])
#guard ((Description.mk [leaf,.thenOp 0 0,.tensor 1 1] 2).occurrences.toOption == some [0,0,1,0,0,1,2])
#guard ((Description.mk [leaf,.provider "main" "unused" [] [] [("U",2)]] 1).occurrences.isOk == false)

end QleisliKernel.Tests.OperationOccurrences
