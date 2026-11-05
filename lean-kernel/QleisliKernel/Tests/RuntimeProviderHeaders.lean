import QleisliKernel.Qirf.RuntimeProviderHeaders

/-! Original mixed-formal order is independent of the named wire list.
The two Op slots deliberately retain the same provider/context value; neither
wire reordering nor equal subjects may remove an original occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeProviderHeaders
open Qirf.RuntimeProviderHeaders

private def names : List String := ["U","V"]
private def duplicateProvider : Nat × List Nat := (7,[3,1])

#guard ((originalBindings names [("V",duplicateProvider),("U",duplicateProvider)]).toOption ==
  some [duplicateProvider,duplicateProvider])
#guard ((originalBindings names [("V",(9,[2])),("U",duplicateProvider)]).toOption ==
  some [duplicateProvider,(9,[2])])
#guard (match originalBindings names [("U",duplicateProvider),("U",duplicateProvider)] with
  | .error .request => true | _ => false)
#guard (match originalBindings names [("U",duplicateProvider)] with
  | .error .request => true | _ => false)
#guard (match originalBindings names [("V",duplicateProvider),("U",duplicateProvider),("X",duplicateProvider)] with
  | .error .request => true | _ => false)

end QleisliKernel.Tests.RuntimeProviderHeaders
