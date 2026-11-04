import QleisliKernel.Qirf.RuntimeInteriorSupply
import QleisliKernel.SourceTypes.GenericProviderChildren

/-! Ordered native child reads retain the original two substitution steps.
Their assembled description and supplier offsets come from the executable fold.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeInteriorSupply
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.GenericOperationSubstitute (BinaryConstructor BinaryChildren ProviderChildren)

private theorem binaryOrder {constructor : Nat → Nat → GenericOperation.Node}
    (kind : BinaryConstructor constructor) (l r : Nat) : (constructor l r).children = [l,r] := by
  cases kind <;> rfl

/-- Left and right refer to the two positions of one parent occurrence. The
two source indices may be equal; the two native reads remain positional. -/
theorem EdgeAt.binaryAssembly {artifact catalogue context description graph implementations references prepared
    root requested checked native sources app original transfer current}
    (left : @EdgeAt artifact catalogue context description graph implementations references prepared root requested
      checked native sources app original transfer current (.child 0))
    (right : EdgeAt transfer current (.child 1)) {constructor l r}
    (kind : BinaryConstructor constructor) (source : left.parent.node = constructor l r) :
    BinaryChildren transfer left.parent l r constructor left.row right.row := by
  have first : left.position = 0 := left.ordinal
  have second : right.position = 1 := right.ordinal
  have parent : right.parent = left.parent := Option.some.inj (right.parentAt.symm.trans left.parentAt)
  have a := left.edgeIndex
  have b := right.edgeIndex
  rw [source,binaryOrder kind,first] at a
  rw [parent,source,binaryOrder kind,second] at b
  have leftIndex : l = left.next.index := Option.some.inj a
  have rightIndex : r = right.next.index := Option.some.inj b
  obtain ⟨x,y,used⟩ := transfer.binary_children left.parentAt kind source
  have xeq := Option.some.inj (used.left.atIndex.symm.trans (leftIndex ▸ left.used.atIndex))
  have yeq := Option.some.inj (used.right.atIndex.symm.trans (rightIndex ▸ right.used.atIndex))
  exact xeq ▸ yeq ▸ used

/-- A provider's selected mixed argument keeps the Op-only position obtained
from the native header. The proof also retains the full assembly of every
other argument, including arguments the provider body does not apply. -/
theorem EdgeAt.providerArgument {artifact catalogue context description graph implementations references prepared
    root requested checked native sources app original transfer current ordinal}
    (edge : @EdgeAt artifact catalogue context description graph implementations references prepared root requested
      checked native sources app original transfer current (.actual ordinal))
    {owner name bases naturals operations premises argumentName childIndex}
    (source : edge.parent.node = .provider owner name bases naturals operations premises)
    (selected : operations[edge.position]? = some (argumentName,childIndex)) :
    ∃ basisRows naturalRows supplied,
      ProviderChildren transfer edge.parent owner name bases naturals operations premises basisRows naturalRows supplied ∧
        supplied[edge.position]? = some (argumentName,edge.row.result.subject) := by
  obtain ⟨b,n,ops,assembled⟩ := transfer.provider_children edge.parentAt source
  obtain ⟨child,atPosition,used⟩ := assembled.operation_at selected
  have index := edge.edgeIndex
  rw [source,GenericOperation.Node.children,List.getElem?_map,selected,Option.map_some] at index
  have sameIndex : childIndex = edge.next.index := Option.some.inj index
  have sameRow := Option.some.inj (used.atIndex.symm.trans (sameIndex ▸ edge.used.atIndex))
  exact ⟨b,n,ops,assembled,sameRow ▸ atPosition⟩

end QleisliKernel.Qirf.RuntimeInteriorSupply
