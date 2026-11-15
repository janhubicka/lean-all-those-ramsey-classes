# Track C — under original A-minimality, no smaller-root obstruction for width-one mixed P

14 November 2026. Stacked on #1186 -> #1184 -> #1183 -> #1182.
Full exact-head Lean build, permitted axioms, source-integrity and
protected-root inventory CI pending. Frozen original 2019 TeX untouched.

The verified positive-B-rank active-boundary dichotomy and its refined
source obstruction classifier (#1162, merged) give a genuine source
rank-decreasing B-to-A replacement OR a smaller positive native
minimal closed separator d with exact complete source root in the
old P and full target seam, injective d-root target coordinates,
genuine d.left B-exclusive, d.right A-exclusive, and either:
(a) d.left's chosen B-side source component captures an old P-root,
or (b) d.left's chosen component contains an A-exclusive source vertex.

Assume additionally original GLOBAL A-exclusive SOURCE-support
minimum among all forbidden original finite sources/weak target maps,
and P a globally nonroot-size-minimum genuinely A/B-mixed source
piece rooted in that seam, with P.width=1.

The new claim2_originalAMinimal_widthOne_no_smallerRootObstruction
eliminates BOTH alternatives. Case (a) is direct B-side capture.
In (b), the actual minimal-mixed source theorem forces B-side
capture by d.left, because d's chosen component already has
an actual B-exclusive distinguished vertex and an A-exclusive
witness. But PR #1186 proves no B-side capture can occur with
a singleton P-root, since original A-minimality forces THAT
old root into d's opposite A-side component and true minimal
separator components are disjoint.

This is a precise native-source obstruction elimination.
Still outstanding: package the full positive-rank Claim 2 theorem
as a direct corollary, establish the initial minimizer/selected
piece state with required local boundary injection, and the
zero-B-rank terminal contradiction. The original positive-rank
B-successor need not preserve GLOBAL A-support minimality, so
one cannot invoke a B-rank minimizer without checking that
separate quantitative condition.

No weak-map global injection, no target-image counts or
m<n claim. One named #print axioms, one protected root,
no reinstated removed TODO.
