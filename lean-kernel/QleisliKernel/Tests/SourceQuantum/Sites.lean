import QleisliKernel.Tests.SourceQuantum.Data

namespace QleisliKernel.Tests.SourceQuantum

theorem canonicalOriginalOrder :
    (tableView source (selector source)).toOption = some [2,0,1] := by decide +kernel

theorem insideKeyword : siteError source "choose" 1 = some .request := by decide +kernel

theorem differentFunction : siteError source "keep" = some .request := by decide +kernel

theorem splitArrow : siteError (source "Tri::C= >keep,Tri::A=>keep,Tri::B=>keep") = some .request := by decide +kernel

theorem extraOwner :
    siteError "unitary fn choose(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qmatch(s,q,q){0=>keep,1=>keep}}" =
      some .request := by decide +kernel

end QleisliKernel.Tests.SourceQuantum
