# Track C: opposite-component nesting after old-root capture

14 November 2026. A genuine source-geometry refinement, draft until
exact-head Lean CI and named permitted-axiom checks pass.

When a true smaller native minimal-separator piece d (with full root
contained in an old outer P) has BOTH distinguished endpoints in
P's chosen original nonroot component, and ALL vertices of P's old
root belong to the selected d.left component, then separator
component disjointness forces the opposite d.right component to
avoid EVERY old P-root vertex.

The verified source-component path induction works on arbitrary
functional Gaifman graphs: any d.right-reachable source vertex
cannot leave the old P-component without hitting an old P-root,
but no such old root is in d.right's component. Thus the entire
opposite d.right component stays inside P's selected component.

The full opposite SOURCE carrier R_d ∪ C_d(right) is a PROPER
subset of the original P carrier: R_d was assumed inside P and
d.left is inside P but outside the d.right component and R_d.

Two new direct theorems:
- `geometricPiece_oppositeProper_of_allOldRootsCaptured`:
  any width, assuming ALL old P roots captured on d.left;
- `geometricPiece_widthOne_capture_oppositeProper`:
  for old root width n=1, capture of its single old root on d.left
  automatically gives the previous premise.

This is a concrete partial localization of the **capture** branch
rather than assuming capture cannot happen. It does NOT prove
that the opposite component is entirely A-exclusive, that it is
already a valid selected-Q **A-to-B** flip, or that its global
rooted canonical symbol equals the original P symbol. It does
not solve n>1 cases with old-root vertices split between the
two d-components. Those need independent treatment.

No quotient of weak target images, no root-width comparison, no
original manuscript changes or reinstated collaborator TODO.

## Stronger true geometric piece, not just a nested source set

The verified source minimal closed separator is symmetric:
`minimalClosedSeparator_swap`. Define
`geometricOppositeMinimalSeparatorPiece Source d` by retaining
the complete ordered d.roots and interchanging d.left and d.right.
This is an ACTUAL `GeometricFunctionalPieceData Source m`, with
all original minimality, closure and root-injectivity data; no
formal-weak target map upgrade.

The direct vertex-carrier identity shows this swapped piece is
literally `d.root ∪ component(d.right)`. The new theorem
`geometricOppositePiece_proper_of_allOldRootsCaptured` proves it
properly nests in P whenever all old P-root vertices are captured
by d.left. Its width-one corollary requires only capture of the
SINGLE old root.

This is a legitimate smaller native piece for further selected
piece geometry. Additional properties for a canonical flip, such
as target-side purity of its selected d.right component, selection
of a matching global canonical symbol and the desired strict
A-support rank contradiction, are NOT asserted.
