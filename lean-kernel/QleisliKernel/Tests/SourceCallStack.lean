import QleisliKernel.SourceTypes.SourceCallStack

/-! Concrete specialization-stack checks supplement original guarded decrease
proofs. They neither admit mutual recursion nor turn a smaller chosen instance
into proof of an original symbolic call.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceCallStack
open QleisliKernel QleisliKernel.SourceTypes SourceCallStack

private def frame (n : Nat) : Frame := ⟨"main","repeat",[("n",n)],true⟩
#guard permits [] (frame 2)
#guard permits [frame 2] (frame 1)
#guard permits [frame 1,frame 2] (frame 0)
#guard !permits [frame 2] (frame 2)
#guard !permits [frame 2] (frame 3)
#guard !permits [frame 0] (frame 0)
#guard !permits [⟨"main","other",[],true⟩,frame 2] (frame 1)
#guard !permits [⟨"main","repeat",[],true⟩] ⟨"main","repeat",[],true⟩
#guard !permits [frame 2] ⟨"main","repeat",[("n",1)],false⟩
#guard !permits [] ⟨"main","repeat",[("n",1),("n",0)],true⟩

#guard decreases [("n",2),("m",1)] [("m",1),("n",1)]
#guard !decreases [("n",2),("m",1)] [("m",2),("n",1)]
#guard !decreases [("n",2),("m",1)] [("n",1),("other",1)]

#print axioms QleisliKernel.SourceTypes.SourceCallStack.read
end QleisliKernel.Tests.SourceCallStack
