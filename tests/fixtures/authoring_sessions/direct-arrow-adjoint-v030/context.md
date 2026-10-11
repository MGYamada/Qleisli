# Direct adjoint of a general operation formal

Informed conformance repair under #83. At baseline 850b103aa7740b4ce982b92794659bb351508d00, the Reference says an Adjointable operation exchanges its exact ports. The retained source uses a principal-Unitary unitor and calls the adjoint of its abstract operation formal directly. It should reconstruct Q<(Unit,Bit)> from Q<Bit>, preserving both basis columns and any external reference; equal physical width is not type equality. Independent review found that passing the same static adjoint through an Applicable helper succeeds while the direct form rejects.

This first source is preserved before repair. Ordinary named runtime-group transforms retain their separate endomorphism restrictions. Iso-only providers must not gain adjoint access; wrong ports, missing capability and false Meaning still reject. Small execution comparisons are not full source preservation or constitutional discharge. This is not a blind authoring benchmark.
