# Track C: one actual selected-Q successor carries the full current induction invariants

14 November 2026. Additive proof, stacked on #1157, exact-head CI required.

New theorem: `geometricGlobalRightFlip_actualOuterPiece_withFullInductionInvariants`.

Input: one ACTUAL finite forbidden native source and a true geometric
outer minimal-separator piece, an eligible one-sided inner piece with
positive width and injective ordered inner target root, a full target
free-amalgam and common canonical lift, a B-exclusive source vertex
in the inner selected component, an A-exclusive SOURCE anchor in the
old outer piece, the LOCAL old B-active complete generated-boundary
injection hypothesis, and the explicit old outer ordered target-root
seam inclusion and injectivity.

Output: ONE actual selected-Q forbidden replacement and ONE new genuine
outer geometric piece. Its B-exclusive SOURCE rank is strictly lower.
It has the same original global canonical piece symbol and ordered
target-root coordinates. Every exterior source count for every target
set is unchanged. It satisfies the SAME local generated B-active
boundary injection predicate. It contains an A-exclusive SOURCE
anchor at the SAME target coordinate. Its complete ordered outer
root lies in the full target seam and is target-injective, and the
entire new geometric outer piece has the verified functional
no-escape property relative to that seam.

Proof: reuse the SAME #1157 witness (do NOT independently choose the
boundary-preserving and anchor-preserving witnesses), then apply the
merged source geometric root-target-coordinate transfer theorems
`geometricOuterRootSeam_noEscape_of_targetCoordinates`
and `geometricOuterRoot_imageInjective_of_targetCoordinates`.

Limitations: this is a one-step successor for an ALREADY ELIGIBLE
inner piece. The hypothesis of OLD ordered-root target injection is
not automatically supplied by a weak EHN source map. It does not
select a flippable piece in the captured-root/A-mixed smaller-root
branches, establish an initial state for arbitrary forbidden witnesses,
or prove the terminal original Claim 2 A-clearing contradiction.

No weak-image quotient or image-cardinality rank is introduced.
The frozen 2019 numbered text is unchanged, no removed TODO restored.
New named axiom certificate and protected active-root entry.

## Adversarial refinement: do not require outer root injection for ordinary iteration

The original positive-rank active-boundary dichotomy does **not** assume
that the ordered current outer root maps injectively into Target.
It is therefore important not to make that an unnecessary induction
hypothesis. The module now exports TWO endpoints:

1. `geometricGlobalRightFlip_actualOuterPiece_withSeamAndNoEscape`:
   same Q, local B-boundary injection, A-anchor, B-source rank descent,
   exterior counts, target seam containment and geometric no-escape,
   WITHOUT any outer target-root injection premise.
2. `geometricGlobalRightFlip_actualOuterPiece_withFullInductionInvariants`:
   a direct corollary that additionally preserves ordered outer-root
   target injectivity WHEN it was known in the old state.

The second is optional and must not replace the first in an argument
that starts from a general weak EHN forbidden source map.
