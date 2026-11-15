# Track C — exact quantitative obstruction to iterating original A-minimality

14 November 2026. Independent original-source Lean proof draft on
main, exact-head Lean/axiom/admission/active-root CI pending.
Frozen 2019 source left unchanged.

The original 2019 Claim 2 argument chooses an F-forbidden native
source/weak EHN target-map pair with *globally minimal* total
A-exclusive SOURCE support, then performs B→A source replacements.
But the verified selected-Q flips do not guarantee preserving
that total A-exclusive SOURCE count.

This module isolates the precise issue as a mathematical result:

* `fullNativeRetainedComplement_Aactive_strictIncrease`:
  given old/new full embeddings of the SAME complement E
  and exact old/new weak target-value agreement on E,
  if ALL old A-active source vertices are in the old E-image
  and ONE new A-active source vertex lies OUTSIDE the NEW E-image,
  then Nat.card of the total A-active SOURCE support strictly
  increases after the replacement.

  Proof: the OLD A-active SOURCE subtype embeds injectively
  into the NEW A-active subtype through its retained E-side
  unique old representative; the extra NEW source A vertex
  lies outside that embedding's range. Finite injective
  nonsurjective cardinal comparison yields strict inequality.
  No EHN map injection or target-image quotient.

* `fullNativeSelectedQ_nonroot_outside_retainedComplement`:
  in an ACTUAL full native free-amalgam Q+_R E, every
  Q-nonroot SOURCE vertex is outside the image of retained E,
  by exact source overlap.

* `geometricSelectedQ_AactiveNonroot_forces_strictAIncrease`:
  in the REAL geometric selected-Q source flip, if the
  removed old nonroot component is A-free and there is
  a NEW Q-nonroot source vertex mapped A-exclusive,
  then the total NEW A-exclusive SOURCE count is STRICTLY
  larger than the old count. No invented weak-map
  identification, and all old A vertices are genuinely
  retained in E.

This is a conditional **obstruction**, not a universal claim
that every selected-Q B→A flip inserts a new A-exclusive nonroot
vertex. It shows that original global A-minimality cannot be
assumed to remain true along arbitrary successful B-rank
decreasing flips unless an additional A-support control
certificate is supplied.

This is relevant to the terminal case PR #1193, which gives a
genuine A-support contradiction at zero B-rank only when the
current source/weak map is STILL globally A-minimal. The
new quantitative lemma explains why that hypothesis may fail
after iteration, and therefore distinguishes a mathematically
valid conditional terminal theorem from a complete 2019 proof.

No original numbered paper edit and no reinstated removed TODOs.
Three named #print axioms and one active source root.

**Necessary neutrality condition:** The module also proves
`geometricSelectedQ_nonIncreasingA_forces_nonroot_Afree`:
if total A-source support does not increase under the genuine
selected-Q replacement of an old A-free component, EVERY
Q-nonroot source vertex must map outside A-exclusive target.
This is a necessary condition, not an existence theorem for
a replacement satisfying it; failure of that existence is the
precise remaining A-minimality iteration obstacle.
