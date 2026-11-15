# Track C — exact A-neutrality iff the inserted selected-Q nonroot is A-free

14 November 2026. New companion module stacked inside draft PR
#1196, based on the original selected-Q strict source support
increase barrier. Exact-head full Lean/axiom and source-inventory
CI pending. Original 2019 source remains frozen.

Prove the exact **necessary and sufficient** SOURCE-side
condition for total A-source support to remain identical during
a genuine full native source replacement Q+_R E of an old
selected component which contains NO A-exclusive source vertex.

(1) General full-complement equality lemma. If every A-active
old and new SOURCE vertex belongs to the corresponding full
embedding image of a single retained complement E, and the
original/new weak target coordinates agree on ALL E vertices,
then the A-active SOURCE subtype sets are images of the SAME
E-subtype. FULL embedding injectivity (not weak target-map
injectivity) gives equal Nat.card.

(2) Actual geometric sufficient condition. If every inserted
Q-nonroot SOURCE vertex is A-INACTIVE, then any new A-active
source vertex in Q must lie on the common ROOT: the exact
native Q+_R E overlap equation identifies that root vertex
with the same source vertex of retained E. All other new
vertices lie in E by the native free-amalgam covers axiom.
The old A-free component assures that every OLD A-active
source vertex already lies in the old E-image. Therefore
the new and old A-active SOURCE counts are EQUAL.

(3) Previous strict-increase theorem proves the converse:
if total A-source count is equal, no newly inserted Q-nonroot
SOURCE vertex can be A-active, because it would force strict
increase. Combine to obtain
`geometricSelectedQ_totalASourceNeutral_iff_nonrootAfree`.

The full if-and-only-if is a conditional statement about
ONE genuine selected-Q replacement with old selected
component A-free, old/new full complement agreement and
actual native free-amalgam. It says nothing about whether
a canonical Q with the required A-neutrality actually
EXISTS at each positive B-source rank. It should not be
conflated with the restricted width-one existence proof
#1189 or the conditional terminal A-clearing result #1193.

This is the precise gate for preserving original global
A-minimality under B-descent: if an A-neutral Q can be
selected, the original support minimum persists, but this
existence must be established separately.

Three named #print axioms checks and one protected active root.
No prior collaborator-removed TODO restored.

## Transfer of original global A-minimality

The additional theorem
`geometricSelectedQ_nonrootAfree_preserves_globalAMinimum`
packages the exact state-level consequence: given a genuine
F-forbidden selected-Q new source/weak EHN map, if the OLD
source map was global-minimum in A-active SOURCE cardinality
among all F-forbidden weak EHN maps to the fixed target,
then NEW Q nonroot A-inactivity, old component A-freeness
and complete E-coordinate agreement give an equal A-support
count and hence the same global A-minimality property of
that very new forbidden witness. No independent source/map
witness is chosen.

The theorem expressly DOES NOT construct an A-neutral Q.
That selection or an alternative induction invariant remains
the missing substantive positive-B-rank iteration step.
