# Track C: global mixed-source minimality forces opposite B-purity under complete old-root capture

14 November 2026. New native formalization stacked on the exact
#1178 → #1175 opposite-side flip/nesting branches. Full exact-head
Lean/axioms/admission/active-root CI is required before merging.

## The genuine mathematical deduction

Let P be globally minimum among the finite ORIGINAL-SOURCE
A/B-mixed geometric pieces rooted in a fixed full seam S. Let d
be another real positive-width minimal closed separator, rooted
inside S, whose two distinguished vertices belong to P's old
selected component. Assume **every old P-root source vertex**
is in d's original selected d.left component, and d.right is
A-exclusive.

The opposite genuine geometric piece d^op is obtained by
swapping d.left and d.right, preserving the COMPLETE ordered
native closed root and separator minimality. If d.right's
component contained a B-exclusive SOURCE vertex, d^op would
be another legitimate A/B-mixed piece with root in S.
The already-checked
`minimalMixedPiece_otherMixed_capturesOldRoot` would then
force some old P-root vertex into d^op's selected component.
But ALL old P-root vertices are in d.left's component and the
two genuine d-components are disjoint. Contradiction.

So `claim2_minimalMixed_allOldRootsCaptured_oppositeBFree`
proves the opposite d.right component is B-FREE, without
postulating target-side purity.

## Actual original A-source support flip

Assume additionally the original native forbidden F-source with
full target free amalgam and common FULL global canonical lift,
the entire d root inside the original P carrier, and injection
of the ordered d-root TARGET coordinates. The new theorem
`claim2_minimalMixed_allCaptured_opposite_actualLeftSupportFlip`
first produces the genuinely properly nested opposite piece
from #1175; uses the NEWLY derived opposite B-purity for the
actual original weak source EHN map; factors the piece through
the full LEFT target; recovers the common-root coordinates; and
invokes the verified global original A-to-B source flip. It
returns a REAL new F-forbidden source with strictly fewer
A-exclusive SOURCE vertices mapping into the same full Target.

The theorem does **not** require the old root width to be one.
It handles **complete** old-root capture in any width. For width
one, every capture is automatically complete; the initial
smaller-root certificate from #1127 supplies the injectivity
of the actual d-root target map.

## Important remaining obligations

* In general old-root width n>1, a selected smaller component
  can capture only SOME old roots. Complete capture is a real
  extra hypothesis, not a consequence of local injection.
* Original A-support minimization must be packaged separately
  to turn the strict A-decrease into a contradiction.
* The zero-B-rank terminal A-clearing proof and initial
  normalization of arbitrary weak witnesses remain open.
* This is a genuine SOURCE count; no weak-target image quotient
  or unproved whole-seam injection is used.

No edits to the frozen original 2019 manuscript or reinstated TODOs.
Two named axiom checks and a protected active root are included.
