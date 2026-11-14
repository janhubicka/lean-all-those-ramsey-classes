# Track C: two-sided old-root capture forces distinct SOURCE root indices

14 November 2026. Independent small original-source geometric module
on main; exact-head Lean/axiom/source-integrity CI pending.

A genuine smaller native minimal closed separator d can in principle
have old P-root vertices inside both its d.left and d.right
selected nonroot components. The two actual d-components are
disjoint, so captured old-root vertices on the two sides MUST
be different. The new theorem
claim2_twoSidedOldRootCapture_distinctIndices returns actual
different indices i!=j in Fin n of the COMPLETE original
P.root enumeration, with the corresponding source Gaifman
component memberships.

Consequently
claim2_widthOne_no_twoSidedOldRootCapture
proves simultaneous old-root capture on opposite sides is
IMPOSSIBLE if the actual original P.root has width one. It
uses no weak map, original family, canonical lift or minimizer.

The relevance to the pending global A-source-minimality
Track C stack (#1184/#1186) is direct: there, a positive
smaller-root certificate under A-minimality forces an old
root into d.right. If the selected B-side d.left also
captures an old root and P.width=1, the two-side capture
certificate supplies the contradiction. For old width >=2,
two DIFFERENT old P-root source vertices can lie in the
opposite components, and this native geometric lemma
does not rule it out.

No unjustified target-image quotient/cardinality or
root-width descent. Frozen 2019 source unchanged.
Two #print axioms checks and one protected active root.
