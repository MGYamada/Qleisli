import QleisliKernel.Tests.SourceQuantum.Data

namespace QleisliKernel.Tests.SourceQuantum
open Semantics.FiniteCarrier Semantics.Raw

theorem observingHeader :
    (signatureView "pub observe fn keep(q:Q<Bit>)->Q<Bit>{q}").toOption =
      some ([[.bit]],[[.bit]],some .observe) := by decide +kernel

theorem missingPublicEffect :
    error (signatureView "pub fn keep(q:Q<Bit>)->Q<Bit>{q}") = some .request := by decide +kernel

theorem ordinaryInput :
    error (signatureView "pub unitary fn keep(q:Bit)->Q<Bit>{q}") = some .request := by decide +kernel

theorem zeroWidthNominal :
    let text := "pub struct Empty{} pub unitary fn keep(q:Q<Empty>)->Q<Empty>{q}"
    let owner := [.record ⟨"main","Empty",text⟩ []]
    (signatureView text).toOption = some ([owner],[owner],some .unitary) := by decide +kernel

end QleisliKernel.Tests.SourceQuantum
