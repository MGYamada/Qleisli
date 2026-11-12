# Imported nominal type used only in the body

This informed probe for #64 keeps a two-qubit coherent selection and returns an
ordinary Bit projected from a record declared in another module. The exported
type contains no Packet. The expected result retains both quantum owners,
the exact conditional phase, and the ordinary Bit value 1.

The first invocation omitted the required schema-2 manifest. Adding it exposed
the original typed dependency refusal with both .qli files unchanged. The
observation timestamps are the stdout files' write times. The baseline
worktree was a0eea04de4678ca92ed4df48d3e59b6d494d17d4. The already built
observer had SHA-256
f5d0fc8ab4b5a15e0255dd941c0162c0f56608d31896874934aee8e45259f643;
the native checker had SHA-256
abbce360dbb4dcf9425872c93e16456b576623f46bd9daeef25b7bdf841658ae.
These are bounded observations, with no source-preservation claim.
