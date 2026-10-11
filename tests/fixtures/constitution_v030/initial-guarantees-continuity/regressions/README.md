# Independent bounded continuity regressions

These are small isolated Lean experiments over the approved historical source
archive, conducted independently of the checker implementation. No production
semantic source was edited. `final-summary.json` is the original result summary;
`index.json` binds the preserved records and storage map.

The final extractor is SHA-256
`6668a374da66c2e6ead95da7da5a7b367cc847c8e8a966654ec46433704e9a77`,
and its baseline has 1,244 declarations. Its uncompressed historical expression
stream is SHA-256
`720cabb37cfd75fb3d9fc509c9d84cace6ccb9776872e5df8361e878890c857b`.

| Case | Actual compiled change | Final result |
| --- | --- | --- |
| `packet-binding-true` | Replace `Acceptance.packetBound` by `True` and adjust its constructor proof | Rejected; the complete constructor type changes |
| `private-u32-offset` | Change the private packet decoder's byte offset from `offset+i` to `offset+i+1` | Rejected; private helper definition changes |
| `proof-maintenance` | Wrap the scope theorem proof in `id`, add an unused theorem, and add a semantic-source comment plus extra spacing in `def   OwnershipSafe` | Accepted; every extracted declaration is identical |
| `unknown-origin` | Keep the original declaration text and namespace, but import it from `Protocol.OtherValidity` | Build succeeds; extraction rejects the unrecognized module origin |

The initial three semantic/proof cases all compiled and retained the exact old
human-review type/axiom output. This demonstrates why that printed output alone
cannot preserve meaning. The final runs use the final extractor and actual
Python comparison function. Final proof-maintenance rebuilt the changed sources
before extraction. The other final runs reused their already rebuilt isolated
mutations and replaced only the extractor. The original 213 historical source
files were checked again and remained unchanged.

`packet-probe/` preserves a separate 13-byte packet experiment. The historical
packet decoder returns `ok: ([120], none)`; the shifted decoder returns
`error: invalid packet length`. Both probe executions complete successfully.
This is a decoder observation, not a successful QIRF acceptance claim. No large
quantum instance or maximum-size case was generated.

Each case's `evidence/` directory retains the first study with the earlier
extractor, while `final-evidence/` records the final 1,244-declaration tool. The
first tool lacked traversal of the current checker's generated body helpers;
its records are preserved as history and are not the final validation. Patches,
mutated source, original commands, exits, diagnostics and hashes are retained.
The initial baseline and comparator were recovered by reversing only the final
identity-metadata change, and their bytes match the earlier recorded hashes
exactly; `storage.json` identifies those preserved artifacts.

Large JSON stdout streams are stored as `extract.json.gz`. `storage.json` maps
each omitted plain `extract.stdout.txt` to its compressed storage and original
uncompressed SHA-256. The execution records retain their actual stdout hashes;
compression does not change the evidence being compared. Absolute scratch paths
inside the original records describe where commands actually ran. The storage
map records their relocation without rewriting those historical records.

These experiments and file hashes do not authenticate machine execution, admit
another guarantee, prove a general representation transport, or complete #141.
The main checker validation and current source binding remain separate.
