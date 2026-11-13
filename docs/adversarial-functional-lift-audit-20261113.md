# Adversarial functional-lift audit and maintenance — 13 November 2026

**Scope and limits.** This is a focused adversarial inspection of the corrected 2019
relational endpoint, the current functional-lift critical path, six open
unmerged Lean proof PRs, public status claims, and the repository's CI/source
integrity and active-root machinery. It is **not** a line-by-line independent
refereeing of every Lean declaration, and it is **not** a proof of the original
unrestricted primitive-function theorem. The numbered manuscript is frozen;
do not reintroduce author-removed TODOs.

## Ground truth and hypothesis boundaries

* `AllThoseRamseyClasses.PublicAPI` exports the proved **coordinated corrected
  relational** Theorem 2.18. Its exact weak tests and the explicit
  isomorphism-invariant class hypothesis are essential; this result is not
  interchangeable with the literal uncorrected printed statement.
* Track F's native fair-chain results, including genuine FULL finite-stage
  embeddings, finite age equality and extension, two-sided stage steps and
  the actual surjective first-order directed-limit map, all retain the
  `GlobalOriginalFiniteFraisseInput F` premise. This is not a consequence of
  the original unrestricted finite-family/source-avoidance claim.
* Track E2 now proves a canonical hybrid **embedding-space/Ramsey-arrow
  equivalence**, canonical-source U-closedness, and the image of genuine
  native free amalgams in the joint hybrid tagged language. These results
  do **not** yet produce a Ramsey witness among arbitrary noncanonical
  hybrid targets, nor a sufficiently normal two-pass tagged witness and
  final same-map native protected homomorphism-embedding.
* No count of green small lemmas establishes the unrestricted Claim 2
  geometric successor, seam-collision termination, or the final
  original finite-family Ramsey conclusion.

## Six outstanding PRs: hostile proof-gate review

| Track | PR | Exact-head obstacle / independently necessary mathematics |
| --- | --- | --- |
| C | [#1089](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1089) | Lean type mismatch for `hNoRankTwo` in `FunctionalWithParts2019VertexCutoffCanonicalRoot.lean`. More importantly, exact **vertex-cardinality** completion is not interchangeable with a stronger generating-rank cutoff: eligible cuts and their hull bounds must be justified separately. |
| C | [#1101](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1101) | `Claim2RetainedCutBoundaryPair.lean` has a boundary type mismatch and a syntax error. Agreement of retained E preimages is a conditional source-geometric step, not yet a legal iterative Claim 2 state invariant, nor does it supply the original minimizer exit. |
| D | [#1097](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1097) | Minimal-support `ih` application type mismatch in `EHNMinimalProperHullSeamExclusive.lean`. A proper crossed source-generated hull plus a boundary edge does **not** yield an inclusion-minimal functional separator or a genuinely selected geometric forbidden piece. Do not turn this into the unrestricted strong-amalgamation conclusion. |
| E | [#1103](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1103) | `nativeIrreducible_implies_uIrreducible_of_sideTransfer` has a type mismatch on the actual induced tagged test. The bridge from original native irreducibility to a labelled tagged U-test must be checked on the **same exact carrier** and with original complete fibres; the upstream `partite-construction` [#634](https://github.com/janhubicka/partite-construction/pull/634) is still open. |
| E | [#1104](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1104) | Inherits the #1103 error and the provisional upstream dependency. Its original-unlabelled native test is a further distinct obligation; do not silently infer part-labelled irreducibility from a forgotten unary-part reduct. |
| F | [#1076](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1076) | The conditional homogeneity construction has a failed first-order/native rewrite and an embedding-application type mismatch. Repair the actual stage-map equality and FULL inverse first, then certify the exact-head result. Even a completed conditional homogeneity theorem would not settle unrestricted Claim 2. |

These six drafts have unresolved **genuine development tasks** and are **not
obsolete** merely because their CI is red. Review them before any closure;
preserve conditional hypotheses and historical proposals. Closing an open
mathematical avenue without a proved superseding theorem is not cleanup.

## Verified cleanup performed in this branch

1. The CI workflow already runs `scripts/audit_library.py`, which scans
   executable Lean after masking comments and strings, rejects actual
   `sorry`, `sorryAx`, `admit` and unreviewed local `axiom`/`constant`,
   and checks the import DAG. The separate raw `grep` admission gate was
   redundant and produced false positives for prose comments. Remove it,
   keeping the stronger executable-source scan and the existing independent
   named `#print axioms` verification. Extend scanner regression tests.
2. Prune **13 provably transitive active-root markers**, not their source
   files, from the E2, F and seam-injectivity stacks. Every pruned module is
   a direct import of a still-protected module, or transitively imported by
   another protected root. The full all-modules Lean build remains unchanged.
   `scripts/cleanup_inventory.py --verify` must continue to pass.
3. Repair README claims describing already-merged Track F back-and-forth
   PRs as drafts, and its outdated statement about exactly seven axiom
   audit files. The historical 199-declaration floor is *not* the current
   number of checked declarations. Fix a missing separator in the PR list.

No Lean theorem declaration, body, or project dependency pin is changed by
this maintenance branch. Do not claim a new kernel proof on the strength of
these documentation/root edits alone.

## Updated progress estimates (non-appendix functional lift)

| Track | Estimate | Risk-adjusted basis |
| --- | ---: | --- |
| A — selected geometry and source flips | 99% | Verified source-flip interfaces; last integration/presentation review |
| B — profiles and canonical symbols | 98% | Verified all-test equivalence and seam-root criteria |
| C — Claim 2 geometric descent | 87% | Key iterative successor, eligible-cut and terminal argument still open |
| D — EHN collision/minimal-witness control | 62% | Major original-source/selected-piece bridge still missing |
| E — hybrid Ramsey/locality transfer | 88% | Semantic and source free-amalgam components verified; actual final two-pass transfer absent |
| F — native Fraisse assembly | 91% | Full stages and surjective FO map verified; final conditional FULL homogeneity draft fails |
| **Unweighted overall engineering estimate** | **~88%** | **Not** a theorem-closure metric or estimate of time remaining |

Compared with the previous **~90%** report, the lower estimate is an
**adversarial recalibration**, not a loss of any checked theorem. The
mathematically hardest missing implications remain concentrated in C/D/E.
The corrected relational main theorem stays fully proved under its
coordinated hypotheses. The unrestricted functional theorem is **not**
certified. If the combined `main` or cleanup-branch CI has not finished,
report its state as pending, not green.

## Reproducible gates before merging this cleanup

```sh
python3 -m unittest discover -s scripts -p 'test_lean_source.py'
python3 scripts/cleanup_inventory.py --verify
python3 scripts/audit_library.py
python3 scripts/audit_lift_contracts.py
lake build AllThoseRamseyClasses
# CI additionally builds all 881 library modules and checks every
# CheckAxioms*.lean certificate, permitted axioms, and import integrity.
```

A protected-root marker is not proof code; do not prune a Lean source merely
because it is absent from the curated user-facing imports. After checking the
full build and axiom certificates, merge only if this branch's own exact-head
checks pass.