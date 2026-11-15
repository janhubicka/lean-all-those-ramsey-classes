# Track C: injectivity supplies the true local boundary and positive B-rank hypotheses

15 November 2026. Independent additive Lean source module based on
the already merged all-width original Claim 2 positive-rank lemma
#1226. Exact-head Lean/axioms/no-admission/active-root/integrity
checks pending; original 2019 manuscript remains frozen.

## Corrected-source starting state

If the original F-forbidden finite source has a TRUE INJECTIVE
weak EHN target map f into the actual full free amalgam, then
f is automatically injective on EVERY generated source
B-component boundary — regardless of its size, function
closure or Gaifman geometry. Consequently the previously
verified all-width positive-B theorem does not need a
SEPARATE scoped boundary-injection assumption.

A genuine positive-width mixed geometric minimal-cut piece P
rooted in the target seam already contains BOTH an actual
A-exclusive SOURCE vertex a and a B-exclusive SOURCE vertex
b inside its chosen nonroot component, by the exact
`MixedGeometricPiece.left_mixed` and `.right_mixed` fields.
The b vertex witnesses a nonempty B-exclusive SOURCE support
subtype, hence strictly positive Nat.card. Every source
vertex is counted separately even if a weak map had collisions;
injectivity is only used to transfer boundary injection.

New theorem
`claim2_originalAMinimal_injective_mixed_allWidths_hasActualFlip`:
given an actual F-forbidden globally A-source-minimum map f,
an injective f, an actual globally minimum-nonroot-size
mixed piece P and the full target free-amalgam/common
canonical lift, the merged all-width positive-rank theorem
delivers a REAL B-decreasing forbidden replacement with
the original global canonical symbol, exact ordered outer
target-root coordinates, all-target exterior SOURCE count
conservation and surviving A-only SOURCE anchor.

Companion theorem
`claim2_originalAMinimal_injective_nonemptyMixed_allWidths_hasActualFlip`
requires only a NONEMPTY collection of genuine mixed pieces
inside the SAME source: the already verified finite minimum
mixed-piece selector chooses P and the previous theorem
provides the real one-step successor. No second source map
or replacement witness is chosen.

This is a conditional bridge for the corrected image-closure
route in draft #1236: surjective EHN family closure plus
closed target ranges would yield an injective global
A-minimum original forbidden witness. Neither input
injectivity nor stronger image closure follows from the
printed weaker tuple-surjective image condition (Track D
has a concrete counterexample candidate).

CRITICAL limits: existence of a mixed source separator
is not established from an arbitrary forbidden map, and
the B-decreasing selected-Q replacement can INCREASE
total A-exclusive SOURCE support. Therefore this is
NOT by itself a lexicographic contradiction or a proof
of original strong amalgamation. The A-neutrality / alternative
potential selection gap remains, as does integration with
the repaired original theorem statement.

Two named #print axioms, protected source root; no
collaborator-removed TODO reinstated.

## 15 November follow-up: adversarial lexicographic accounting

Four additive source lemmas now give exact natural-number accounting for
an all-target exterior-conserving replacement. In particular,
`claim2_lexMinimal_strict_A_growth_of_local_B_decrease` proves:

* If the OLD original witness is globally lexicographically minimal
  in (A-exclusive SOURCE count, B-exclusive SOURCE count),
* the NEW forbidden source still maps EHN into the SAME target,
* exterior A/B source counts are equal, and
* interior B-exclusive SOURCE count drops strictly,

then the NEW interior A-exclusive SOURCE count MUST GROW STRICTLY.
The companion theorem gives at least one new A-exclusive source vertex
numerically. The elementary opposite conditional contradiction for
non-growing A support is also registered.

This is an OBSTRUCTION, not a closure of Claim 2. The standard
B-to-A flip cannot be iterated within the global A-minimal class just
from exterior conservation and strict B rank descent: if it were
A-neutral, lexicographic minimality would immediately contradict the
reported strict B decrease. One needs either an independently
A-preserving *different* surgery (which would itself immediately
contradict the minimum), or a genuinely different globally
well-founded potential tracking the accumulated A cost. Avoid
claiming the original A-minimum is carried through a B-flip.

All four lemma names are now included in the explicit axiom-check file.
The previous exact-head build job for commit b0a3a1b7 completed
successfully; at the observation point the inventory job was still
queued. The newly pushed source and axiom-check commits require their
own exact-head CI before integration.
