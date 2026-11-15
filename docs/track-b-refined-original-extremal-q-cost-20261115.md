# Track B/C: original all-width extremal source selects SAME Q and pays private A cost

15 November 2026. Stacked draft on #1257 → #1250 → #1248
→ #1241 → #1237 → #1231. Frozen numbered 2019 source unchanged.

## Audit: why the earlier coarse obstruction cannot be eliminated

The existing Track B predicates `claim2NativeOldRootCapture`
and `claim2NativeAMixedRoot` report a positive smaller root
d and capture/A-mixedness, but discard the actual fact that
d.left is B-exclusive, d.right is A-exclusive, both lie in
the ORIGINAL old outer selected component, and that d has
injective ordered TARGET root images. The checked all-width
Track C lemma `claim2_originalAMinimal_allWidths_no_smallerRootObstruction`
needs ALL these source-geometric assumptions. Applying it to
a coarse obstruction predicate would be unsound.

New `Claim2RefinedEligibleInnerSelection.lean` returns:
- an ACTUAL eligible B-only nested inner minimal-separator
  piece BEFORE any forbidden selected Q is chosen; OR
- a REFined true smaller-root witness preserving both original
  B/A distinguished endpoints, old-outer component
  membership, root inside old outer piece/seam,
  injective ordered smaller root target tuple, and
  literal old-root capture or A-mixedness.

The refined proof uses precisely the EXISTING native
partner-versus-smaller generated-boundary source geometry;
it never chooses an invented second Q or a fake quotient.

## Original source extremality, all widths

New `Claim2OriginalExtremalSelectedQCost.lean` composes
the refined selector with the already-verified Track C
all-width extremal source theorem.

If an ORIGINAL finite forbidden weak EHN SOURCE/map is
globally A-exclusive SOURCE-support minimal and its actual
outer source-geometric piece corresponds, by EXACT ROOT-SET,
SELECTED COMPONENT-SET and PIECE VERTEX-SET equalities, to a
mixed source-geometric piece globally MINIMAL in
NONROOT SOURCE cardinality among mixed pieces in that
SAME source/map, then a positive B-exclusive SOURCE rank
CANNOT take the refined smaller-root obstruction branch.
Thus the first true original extremal mixed piece has an
eligible B-only inner geometric source separator. Applying
the SAME selected-Q provenance theorem produces a real
forbidden native B→A weak-EHN source replacement retaining
the original selected global symbol, full Q+old E native
source free-amalgam, A-free removed component, exterior
source support and original anchor/root invariants.

If that ORIGINAL witness also minimizes B-exclusive total
SOURCE support among global A minima (a true original
(A,B)-LEX minimum), the new selected-Q replacement MUST
pay a STRICTLY POSITIVE private Q-nonroot A-exclusive
SOURCE cardinality. This is derived from exact Q-source
A-cost and strictly decreasing global B-source count.

**Key limitation:** the original extremal hypotheses
are used only at the INITIAL state. No theorem asserts
that the new source/map is STILL globally A-minimal or
that its selected outer geometric piece is STILL globally
minimum mixed size. In fact the positive private-Q
A-cost prevents carrying ORIGINAL A-minimality to
the next source by default. This closes neither
the unrestricted iteration nor Claim 2 itself.

Additional initial collision and mixed-piece existence
hypotheses are still open. No weak target-image quotient,
no unverified all-width inference, no new axioms or
edits to frozen collaborator text. New proof roots and
named #print axioms are registered. Hold DRAFT until
exact-head full Lake/Lean, source-integrity/axiom/
inventory CI and all stacked parents are green.

## Dependent-width correction

The native heterogeneous state has an indexed outer piece of width
`n`, whereas `MixedGeometricPiece.data` has its own width
`P.width`. The two indexed Lean records cannot be equated without
a separate transport of the width equality. The extremal wrapper
therefore requires **exact equality of the selected source root
SETS, selected functional component SETS, and entire geometric
piece vertex SETS**. These are precisely the source-geometric
hypotheses needed by the all-width extremal lemma, and are
well-typed even if the two positive root widths are expressed
differently. This keeps the full source geometry honest without
assuming a silent width cast or an identical data term.
