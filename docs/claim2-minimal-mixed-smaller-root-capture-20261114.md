# Track C: smallest mixed original source piece forces capture of a mixed smaller cut

14 November 2026. Independent actual-source lemma, pending exact-head
Lean build, root inventory, no-admission and permitted-axiom gates.

Already merged `RootRetentionLocalization` proves that for two genuine
`MixedGeometricPiece` structures P,Q, if P minimizes the number of
actual nonroot SOURCE vertices among all pieces rooted inside the same
set S and mixing prescribed AOnly and BOnly source sets, and both
distinguished Q endpoints lie inside P's original selected nonroot
component, then Q's selected component contains a genuine OLD P-root
vertex. This is independent of weak source-target map injectivity.

The new module packages that theorem for the precise selected smaller
native geometric piece d, instead of assuming a prepackaged Q:
`claim2_minimalMixed_smallerMixed_capturesOldRoot` accepts d,
positive root width, complete d-root seam containment, original old
P component endpoint containment, and explicit A/B source witnesses
inside d's chosen nonroot component. It returns a real old P root r
inside d's component, in the original S, outside d's own root and
certifies that OLD root retention fails.

`claim2_minimalMixed_no_noncapturing_smallerMixed` proves the exact
contrapositive: **under global nonroot-size minimality** an A/B-mixed
smaller-root piece cannot be noncapturing.

This is important for proof strategy. The noncapturing mixed-piece
finite size descent built separately in #1164/#1166/#1167 is an
honest local result, but on a globally *minimal mixed* outer piece
the noncapturing mixed option is actually impossible. Therefore the
unresolved branch is not simply an endlessly nested mixed-piece
induction: one must analyze the captured old-root seam-incursion
pattern. The capture-path PR #1172 isolates its native witness.

Neither theorem excludes actual capture, proves original 2019
Claim 2, derives old-root target-image injectivity or supplies a
zero-B-rank terminal contradiction. The frozen numbered manuscript
is unchanged and no removed collaborator TODO is reinstated.
