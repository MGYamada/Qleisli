# Work for two computed predicates in a Grover iteration

The first [two-bit](width-2/main.qli) and [three-bit](width-3/main.qli)
programs specialize the same predicate and use a second structurally
synthesized predicate for the phase-fixed reflection. Both
[original](width-2.before.stdout) [diagnostics](width-3.before.stdout)
are the unchanged JSON from `qleisli check <project> --format=json` on
`3ba42da6841c800c98632880871ebe3bac11fc33`. The original independent
native check reached its shared work limit on these small programs.

In both programs one quarter of the rows are marked. After the first
phase operation, the mean amplitude is half the original uniform
amplitude. Reflection about that mean doubles each marked amplitude
and leaves zero amplitude on the other rows. In low-first order the
two-bit outcome is `(1,0)`; the three-bit outcomes are `(1,0,0)`
and `(1,0,1)`, each with probability one half. The test checks
the original source, the two circuit-backed Raw scopes and these
distributions through the native project path.

With separate owner and circuit charges and reuse of the checked source
bodies, the complete project checks consume 8,939,018 and 18,852,558 work,
respectively. Both use the standard 20,000,000 cap.
