# Track C: resolve the smaller-root branch WHEN it does not capture an old root and is A-free

**13 November 2026. Standalone conditional native Lean draft, exact-head CI pending.**

The verified local positive-rank Claim 2 dichotomy (#1106) returns
either a genuine B→A source flip or a smaller positive rooted piece d
whose root lies inside the original outer geometric piece P, with
d.left B-exclusive and d.right A-exclusive in the old P component.
The smaller-root piece is NOT automatically proper or one-sided:
its selected component can swallow old outer-root vertices and/or
contain A-exclusive vertices.

New theorem:
`claim2_smallerRoot_noOldCapture_noA_hasActualGeometricFlip`.

Assume explicitly that:
1. d's entire closed source root lies in P and d.left/d.right both
   belong to the old selected P component (these are the actual
   smaller-root certificate fields);
2. d's left selected component captures NO vertex of P's complete
   old ordered source root;
3. d's left selected component contains NO A-exclusive SOURCE vertex;
4. d's ordered root maps injectively into the target common seam;
5. the old d.left is B-exclusive and d.right A-exclusive;
6. a genuine common FULL global canonical lift exists and d has
   positive width.

The already kernel-checked
`geometricPiece_escapingComponent_capturesOldRoot`
implies from (2) that d's selected component stays in P's
old selected component. Together with (1), its complete
root-plus-component source carrier is contained in P.
Since d.right lies in P but outside d's selected component
by genuine minimal separation, the containment is PROPER.

The checked same-selected-Q full-native
`geometricGlobalRightFlip_actualOuterPiece_withExteriorAndAnchor`
then flips this B-only inner piece d, producing a **real forbidden
replacement source and actual geometric outer piece**, with:
- unchanged original ordered outer target-root coordinates;
- same original globally indexed canonical outer piece symbol;
- strict reduction of B-exclusive SOURCE count inside the new P;
- exact preservation of exterior SOURCE counts for ALL target sets;
- the actual source vertex d.right surviving as A-exclusive
  anchor inside the new P, with its original target image.

This theorem does not use global initial A-support minimizing
witnesses or smallest-mixed-piece assumptions.

**What remains genuinely unproved:** the smaller-root certificate
does NOT itself exclude old-root capture (indeed, the checked
obstruction often forces capture), nor guarantee that the selected
d-component stays A-free. If EITHER fails, the new result does
not produce a successor. Hence this is a correctness-preserving
conditional repair, not the unrestricted 2019 Claim 2 theorem.

All witnesses are literal SOURCE vertices; no folding quotient,
distinct-target-image rank, or assumption of full global weak
source-map injectivity. The numbered 2019 text remains frozen.
One named axiom check, protected root inventory, and full
exact-head Lean build/no-admission CI required.
