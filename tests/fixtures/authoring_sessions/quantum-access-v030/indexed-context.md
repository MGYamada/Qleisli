# Indexed access continuation, before implementation

Informed #29/#69/#74 study at aba190294efd9f3547d528c49fade1de8f596f7d.
The author has read the common source AST/checker, selected Raw lowering,
independent source-step replay and the adopted compile-time place contract.
No external model is invoked; exact model/sampling settings are unavailable.
The first two sources are desired indexed/slice forms, not implemented APIs.
The explicit take/put controls use existing primitives and the whole-owner
control form. All four sources are fixed before the first observation.

Independent expected maps: indexed X toggles axis 1 and no other axis;
the identity slice and explicit round trip preserve every coefficient;
the explicit controlled Z multiplies precisely labels with bit 1 set by -1.
An external reference is unchanged, even for entangled inputs. These are
intended equations, not observations or a general preservation proof.
Selecting/repartitioning axes needs no physical SWAP, preparation, measurement
or new trusted primitive. Exact bounds and same-parent disjointness remain
source obligations. Baseline parse/profile refusals establish none of them.
No QFT, deferred feature, maximum-sized case or new source corpus is involved.
