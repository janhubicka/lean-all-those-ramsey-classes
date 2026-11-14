# Track C — noncapturing mixed smaller root is itself a strictly smaller positive state

14 November 2026. Stacked on #1166 (which is stacked on #1164).
Exact-head Lean/build/axiom CI still pending; original 2019 source frozen.

New theorem
`claim2_smallerRoot_noCapture_mixed_has_smallerPositiveState`.

INPUT: an actual smaller native closed-separator piece d whose
complete root lies inside old P and the full target common seam,
with injective ordered target root, both d.left/d.right in the old
P-component, and NO old P-root SOURCE vertex captured by the chosen
nonroot d-component. Assume the original local complete B-boundary
injection predicate on P, the actual full target free amalgam,
a B-exclusive SOURCE vertex d.left, and an A-exclusive SOURCE
vertex a inside the selected d-component.

OUTPUT, all for the SAME original forbidden source and weak map:
* d is an ACTUAL PROPER source-subpiece of old P;
* the full number of ORIGINAL SOURCE vertices in d is strictly
  smaller than in P;
* its complete root is still in the full target seam and has
  injective ordered target coordinates;
* the actual A-exclusive mixed source vertex a is INSIDE d and
  serves as its A anchor;
* the actual B-exclusive distinguished vertex d.left is inside
  d, so the B-exclusive SOURCE rank inside d is strictly POSITIVE;
* the entire LOCAL generated B-active boundary-injection hypothesis
  restricts to d.

The full free-target overlap is used to identify original RIGHT-only
d.left with the symmetric LEFT-only target-exclusive region, then
the genuine finite SOURCE subtype witness proves positive Nat.card.
No weak-map global injection or target-image quotient/count occurs.

This makes the A-mixed / no-capture branch eligible for ANOTHER
application of the verified positive-rank geometric dichotomy to
the STRICTLY SMALLER source piece d. It does not prove that
successive smaller-root choices never capture a previous root,
does not identify the new d symbol with old P's globally indexed
symbol, and does not prove the terminal Claim 2 contradiction.

One named axiom gate, one protected active-root registration,
and no collaborator-removed TODO reinstated.
