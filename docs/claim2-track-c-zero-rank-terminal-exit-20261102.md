# Track C — terminal zero B-rank implies an actual A-minimality contradiction

New Lean module: `Claim2TerminalZeroRightSupport.lean`.

The finite local B-rank is

```text
Nat.card {v : SourceCarrier //
  v ∈ geometricPieceVertices Source OuterPiece ∧
  f v ∈ fullFreeRightExclusiveTarget iRight jRight}
```

This counts source vertices, not target images. If this number is zero, then no source vertex in the selected nonroot component can map B-only. The proof reflects right-exclusive target membership through the **actual common-root overlap** of the full target free-amalgam. It never injectivizes the global weak EHN map.

Under the original global canonical lift, an actual **terminal positive-width geometric outer piece**, root-injective image and original shared-root inclusion, the parent module's real A→B source flip constructs a new finite forbidden EHN witness with **no A-only source vertex in its selected replacement piece** and the same exterior A-source support. Equality of this exterior support with the original witness's exterior count and positivity of the original inside A-count contradict the original global A-support minimum.

This removes the extra terminal `hNoRight` assumption from the terminal exit API, replacing it with the actual rank-zero certificate.

### Still unproved

The recursive iteration theorem yields a terminal state having **no admissible next step**, not automatically zero B-rank. The remaining substantive Claim 2 obligation is: in every still-positive-B valid geometric outer state, construct an actual proper B-only source subpiece, prove its root target-image injectivity, and show the B→A flip preserves the genuine outer piece, its full all-test profile and exact exterior A-count. That grants a next step and forces the terminal rank to vanish. This is the geometry/collision challenge in Tracks A/D, not an arithmetic assertion.

Exact-head Lean build/axiom audit pending. Frozen manuscript prose remains untouched.
