# Standard-library contract template

Copy the eight sections below and replace the bracketed prompts before
review. Link the concise English source documentation to this full contract.
Use [the conventions](../STDLIB.md) and existing
[filled examples](../STDLIB.md#template-and-reference-implementations).
This is a documentation template, not an evidence format or adopted new API.

## Meaning

[Operator or complete instrument equation; fixed phase/sign; admissible inputs,
reference extension and logical/physical encodings; contract version.]

## Interface and encoding

[Source link, declaration/classification, exact type tree, parameter roles,
consumed/returned owners, integer bit weights, output axes and display order.]

## Premises and capabilities

[Accepted widths/domain/entry states; totality, control/inverse access premises;
invalid input and unsupported/limit behavior.]

## Ancillas and effects

[Scratch count/initial state, permission, exact final state and separation;
retained data/reference behavior; effect and all measurement/discard outcomes.]

## Approximation

[None, or ideal target, metric, certified error budget and composition/reference
behavior. Keep approximation separate from exact scratch return and device noise.]

## Resources

[Count model, units and input dependence; data/peak scratch, gates, depth,
measurements and host/search work included. Label unknowns and bound proof status.]

## Validation and proof status

| Aspect | Status | Scope and evidence |
| --- | --- | --- |
| Source checking | pending | [Actual source/IR path, widths and result record.] |
| Semantic tests | pending | [Independent formula, exact/numerical domain, tolerance, phase/order/reference/cleanup positives and type-correct faults.] |
| Actual IR conformance | pending | [Theorem about actual IR/checker definitions and premises, or precise missing obligation.] |
| Source preservation | pending | [Source-to-IR correspondence theorem/validation, or precise missing obligation.] |
| Specification review | pending | [Review of mathematical intent and family conventions, or review still required.] |

Use `checked`, `tested`, `proved`, `reviewed`, `pending` or `not-applicable`
as descriptive statuses, with scope and grounds in the last column. A linter
validates the table's form, not its claims. Link every completed result to its
record; explain `pending` and `not-applicable`. Never infer one row from another.

## Adoption and teaching

[Concept/motivation, short derivation and readable code; multiple uses and
held-out composition; experimental/adopted state, differences from existing
APIs, compatibility/migration, source-specific license/notices and open work.]
