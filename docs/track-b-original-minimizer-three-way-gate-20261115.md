# Track B: original minimizer initialization without injectivity hypotheses

**15 November 2026. Stacked on draft #1199 → #1158.**

The new Lean module `Claim2OriginalMinimizerThreeWayGate.lean` packages the
SAME original finite forbidden EHN source/map with a genuine geometric
outer minimal-separator piece, root in the target common seam, and a real
A-exclusive source anchor, **without requiring target injection of the
ordered root or any complete generated B-active boundary**.

The theorem `claim2NativePreRoot_originalMinimizer_rootGap_or_boundaryGap_or_descent`
provides an exhaustive three-way alternative for an ORIGINAL globally
A-exclusive SOURCE-support-minimal forbidden EHN witness:

1. TWO DIFFERENT literal old source root vertices have equal target
   images, and **no** genuine FULL irreducible embedded source test
   contains both; this uses the already merged Track D geometric
   root-test-gap theorem.
2. The old ordered target root is injected, but TWO distinct source
   vertices in the SAME generated B-active boundary within the actual
   old outer geometric piece have equal weak target images, and no
   genuine FULL irreducible embedded source test contains both;
   the boundary is contained in the seam preimage and old outer piece.
3. The old root and all active generated B-boundaries are injected.
   Then the SAME original witness, not a new quotient or substitute,
   enters the concrete finite selected-Q B-source-rank descent. A
   reachable state has a genuine old-root-capture or A-mixed smaller
   component. The entire ORIGINAL global selected symbol, ordered
   root target tuple, source exterior multiplicities for ALL target
   subsets, A-anchor target coordinate, and strict rank budget are
   transported along the genuine steps.

The two missing initial injection assumptions have therefore been
replaced by explicit negative FULL-source-test certificates. This does
**not** prove they are absent. The chosen actual outer geometric piece,
its root-in-seam and A-anchor, connectedness/finite forbidden family
conditions, target free amalgam and original global canonical lift,
and global original A-support minimality remain required.

The later geometric capture/mixed obstructions are likewise genuine
unresolved outcomes (especially partial old-root capture at higher
width). No image quotient, auxiliary forbidden family closure,
claim of universal injection, or unverified general strong AP is made.

## CI and scope

Add named `#print axioms` and active-root registration. Hold this
stacked PR as DRAFT until exact-head Lake/Lean, source-contract,
no-admission, allowed-axiom, and inventory CI all pass, and its parent
drafts are integrated. Frozen numbered 2019 manuscript and
author-removed TODOs are unchanged.

## Width-one specialization

The new `claim2NativePreRoot_widthOne_minimizer_boundaryGap_or_descent`
eliminates the root collision branch **without source test coverage**
when the original outer separator root has width one. The reason is
purely finite-coordinate: every map on `Fin 1` is injective. What
remains is a concrete B-active generated-boundary missing-FULL-test
collision, or a finite native geometric descent to old-root capture
/ A-mixedness. This does not eliminate either remaining branch.

## Proof-control qualification

The heterogeneous relation
`claim2NativeGeometricStep` records the exact native forbidden
source, selected outer geometric piece and the conserved original
symbol/support/root/anchor invariants. The current relation does
**not itself store the selected Q free-amalgam diagram** at each edge.
The positive-rank progress theorem obtains its outgoing step from a
verified actual same-selected-Q construction, but the generic
finite-chain data type permits any edge meeting the displayed
contract. A future stronger chain relation should retain the
literal selected-Q witness per edge if that stronger provenance is
needed downstream. Do not silently equate contract-only edges with
a stored same-Q reconstruction.

The full latest-head Lean/axiom and inventory checks remain required.
