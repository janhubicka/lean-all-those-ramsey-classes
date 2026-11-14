# Track C: an A-mixed smaller root still nests properly if it captures no old outer root

14 November 2026, independent additive source-geometry Lean lemma.
Frozen 2019 paper unchanged; exact-head CI still required.

`claim2_smallerRoot_noCapture_proper_and_localBoundaryInj`
takes a genuine smaller positive minimal closed-separator piece
d of the SAME old original forbidden source and true outer P,
with all native d-root source vertices in P, both distinguished
d.left and d.right in P's selected component, and no old P-root
SOURCE vertex lying in d's selected nonroot component.

From the checked escaping-component => captured-old-root lemma
the entire selected d-component is contained in the old P-component.
The new d-root was already in P, so the entire actual geometric
d carrier lies inside P. This inclusion is PROPER because the
genuine d.right lies in the old P-component but, by the TRUE
minimal separator property, is outside the d-root and selected
d-component.

The local injectivity of the original weak target map on the FULL
function-generated boundary of EVERY B-exclusive component based
in P restricts to the very same local condition for every B-based
SOURCE vertex in d (by the genuine source-set inclusion). No
source/target weak-map quotient and no new arbitrary injectivity
hypothesis.

Crucially, no assumption that d is A-free occurs in the statement.
The A-mixed smaller-root obstruction from PR #1162 can therefore
be treated by a PROPER-NESTED smaller state whenever the old root
is not captured, rather than prematurely declaring failure of
local B-boundary injection. This does not prove that the new
smaller state has an appropriate anchor or positive B-source
rank; those require the actual mixed witness and B distinguished
vertex to be packaged next. It also does not solve the
old-root capture branch or terminal zero-rank contradiction.

One protected active root and one named #print axioms gate.
