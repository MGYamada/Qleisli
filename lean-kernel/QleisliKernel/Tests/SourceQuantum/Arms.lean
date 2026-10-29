import QleisliKernel.Tests.SourceQuantum.Data

namespace QleisliKernel.Tests.SourceQuantum

theorem incomplete :
    let text := source "Tri::A=>keep,Tri::B=>keep"
    error (tableView text (selector text)) = some .request := by decide +kernel

theorem overlapping :
    let text := source "Tri::A=>keep,Tri::A=>keep,Tri::C=>keep"
    error (tableView text (selector text)) = some .request := by decide +kernel

theorem observingArm :
    let text := source "Tri::C=>keep,Tri::A=>keep,Tri::B=>keep" "pub observe fn keep(q:Q<Bit>)->Q<Bit>{q}"
    error (tableView text (selector text)) = some .request := by decide +kernel

theorem wrongTargetTree :
    let text := source "Tri::C=>keep,Tri::A=>keep,Tri::B=>keep" "unitary fn keep(q:Q<Bits<1>>)->Q<Bits<1>>{q}"
    error (tableView text (selector text)) = some .request := by decide +kernel

theorem staleOriginalEnum :
    let changed := "// λ original qmatch in comment is not a site\npub enum Tri { B,A,C } " ++
      "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}" ++
      " pub unitary fn choose(s:Q<Tri>,q:Q<Bit>)->(Q<Tri>,Q<Bit>){qmatch(s,q){Tri::C=>keep,Tri::A=>keep,Tri::B=>keep}}"
    error (tableView changed (selector source)) = some .request := by decide +kernel

end QleisliKernel.Tests.SourceQuantum
