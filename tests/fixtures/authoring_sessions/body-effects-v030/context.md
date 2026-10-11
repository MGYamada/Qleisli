# Context before first observation

This is informed authoring under the approved 110-Issue plan, with repository
and prior-source access. No external model was invoked. The deployed model
identifier and sampling configuration are unavailable; this is not a blind
model benchmark or a success-rate measurement.

The baseline is 21a488024b278fecf0ea5e43be6cc2e846bcc3fe, edition 2026,
product 0.3.0-alpha. The source parser currently requires effect prefixes.
The finite lowerer checks actual body effects but propagates annotation classes;
the sized checker likewise uses declared callee effects. Existing source-only
documentation parses signatures without performing type/ownership checking.
All first sources and schema-2 manifests are preserved before any checks.

Desired effects concern the quantum action at fixed ordinary inputs. Ordinary
copying does not make that action irreversible. Required small cases distinguish
preparation, observation, pure Unit introduction, scalar phase, opaque Apply,
typed same-width/expanding coherent lifts, dependency recursion and call effects.
All body arms and zero-fold bodies remain checked. Missing access, duplicated
owners, narrower assertions and unsupported recursion must still reject.

The proposed ordinary decision retains optional effect annotations as checked
upper-bound assertions. Their normative weakening relation is
Unitary <= Iso <= Observe; principal facts are not inflated by annotations.
Effect inference is not arbitrary operator/Meaning inference, inverse/control
evidence or externally certified unitarity/isometry. #283 remains unresolved
post-v1. No primitive or constitutional guarantee is admitted by this study.
