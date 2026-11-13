# Track B/C: localize the remaining positive-rank collision obstruction

**13 November 2026.** This is a new additive theorem, based only on
already validated main. No change to frozen 2019 source manuscript.

## Why a local collision trichotomy?

The old original-source trichotomy
`claim2_positiveRank_actualSuccessorWithExterior_or_smallerRoot_or_seamCollision`
has a third branch `¬ Set.InjOn f S`, meaning a collision ANYWHERE
in the full common-seam preimage S. That is stronger/more diffuse
than the actual geometric partner flip needs.

The checked stronger conditional theorem
`claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective`
assumes `Set.InjOn f T_x` only for the complete generated boundary
of every B-exclusive component x IN the chosen old outer piece P.

## Exact new statement

`claim2_positiveRank_actualFlip_or_smallerRoot_or_activeBoundaryCollision`
requires the same genuine finite connected forbidden source
geometry, positive B-exclusive SOURCE rank inside P, old positive
root width and surviving A-exclusive SOURCE anchor. It does not
assume full target-seam injection OR active-boundary injection.
It returns one of three cases:

* The existing actual SAME-selected-Q B→A source replacement
  preserving exact global selected symbol, full native outer
  geometry, all exterior SOURCE counts, strict B-only SOURCE
  rank decrease and an A-exclusive SOURCE anchor.
* The existing smaller positive native geometric separator
  with its exact generated opposite boundary.
* A LITERAL selected B-only source component x inside the old
  outer piece P and its exact generated boundary T, with
  T⊆S∩P, and two distinct SOURCE vertices u≠v in T such that
  f u = f v.

The proof splits on the exact active-boundary-injection
condition. In its positive branch, the already verified
two-way theorem returns the flip or smaller root. In its
negative branch, the failure of `Set.InjOn f T_x` produces
u,v on the precise boundary, and the checked geometric outer-piece no-escape theorem
ensures the entire generated boundary T lies in BOTH
S and the original selected geometric source piece P. No weak-image quotient,
distinct target-image counts or new hypotheses are needed.

## Remaining obligations

The new third alternative is a **LOCALIZED** collision,
not a contradiction to the 2019 hypotheses. Initial
active-boundary injection is still not derived. It remains
possible for f to identify nonadjacent source vertices
in a weak EHN homomorphism-embedding, even when the
ordered outer root target image is injective.

The smaller-root piece can still capture old outer-root
vertices or have an A-mixed selected component. That
geometry is being handled separately by draft #1133
and the stacked detailed obstruction classification #1136.
No unconditional Claim 2 or full strong AP is claimed.

## CI

Draft until exact-head complete Lean project build,
the named permitted-axioms checker, source/active-root
integrity and no-admissions checks pass. Do not restore
author-removed TODOs or edit ramsey.tex.
