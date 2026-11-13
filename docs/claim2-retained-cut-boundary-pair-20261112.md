# Track C: paired full-native active boundary transport under matched retained cuts

**12 November 2026. Draft stacked on PR #1093; exact-head Lean CI required.**

Let two genuine full-native functional source free amalgams have the
same unchanged complement E but different inserted pieces Qold and
Qnew. Their respective deleted vertex cuts Sold and Snew can be
arbitrary, need not be closed, and need not contain the inserted
side. Assume each contains its entire glued source root and that

  iOldE⁻¹(Sold) = iNewE⁻¹(Snew).

The proposed
`fullNativeReplacement_retainedCut_generatedBoundary_pair`
returns the SAME actual subset T of E whose full source image is
the complete function-generated external boundary of the
corresponding S-avoiding component of x in each ambient source:

  OldBoundary = iOldE '' T,
  NewBoundary = iNewE '' T.

This follows by applying the parent #1093 exact arbitrary-root-cut
component and generated-boundary image lemma to each source,
then rewriting the new retained cut as the old one.

**Why this is more useful than the old private-boundary theorem:**
the current Claim 2 source cut is the PREIMAGE of the target common
root under its weak map. Such a cut may remove only a portion of
the inserted Q, not the entire Q, and source common-seam collisions
may change its nonretained part. Nevertheless, exact agreement of
weak target maps on all E vertices gives the required equality
of deleted sets ON E, even when the new weak map is noninjective
elsewhere. Thus a B-only component surviving on the unchanged
E can have its true generated boundary transported literally.

This is a source GEOMETRY statement. To obtain the desired
weak-target injectivity preservation, compose it with the
already verified private boundary injection-transfer theorem
and complete old/new E coordinate agreement. To prove the
unrestricted Claim 2, one must additionally select a genuine
B-only flippable subpiece in the mixed smaller-root branch
and handle the terminal A-only clearing exit.

No weak-image quotient, no distinct-target-image counts,
no global old/new target injectivity, no changes to the frozen
2019 manuscript, and no restoration of collaborator-removed TODOs.


## Added source-specific target-seam injection transfer (same draft)

`fullNativeReplacement_activeSeamBoundary_injection_transfer`
specializes the two generic source cuts to literal old/new
preimages of one TARGET common seam under weak maps f,g.
Assume both maps agree on all complete retained E vertices;
each actual glued source root maps into the target seam, and
the chosen E-private source vertex x maps outside the seam.

Their deleted sets automatically agree ON E, even if the new
map has additional Q-only seam-valued vertices. The paired
source theorem produces ONE exact E-generated boundary T
for the old and new true seam-avoiding components. If f is
injective only on the OLD active boundary, g is injective
on the corresponding NEW active boundary. No full new-seam
injectivity, Q root-reflection, or source global injection is
assumed. This also avoids requiring that the old map injects
its entire old common-seam preimage.

This is the desired one-step local-boundary injection
invariant for a given E-private retained component. It remains
necessary to show that all B-active components throughout a
sequence of selected-Q flips can be tracked through these
retained source components, especially when the smaller-root
branch creates mixed pieces. Exact-head Lean CI must verify
this extension before using it in the 2019 Claim 2 induction.


## Universal surviving-active-source boundary invariant

The next strengthening
`fullNativeReplacement_allActiveSeamBoundaries_injection_transfer`
quantifies over **every** new source vertex with weak target image
inside an arbitrary chosen `Active` region, assuming the entire
newly inserted Q side avoids `Active`. Full new-source free-amalgam
coverage ensures each active vertex is an unchanged E vertex.
Old/new target coordinates agree on E, so it was active in the
old source too.

Assume that the old map injected the complete generated boundary
of the seam-avoiding component of each active retained E vertex
(that maps outside the seam). The previous exact paired-boundary
theorem and single-component injection transfer now prove that
the new map injects the complete boundary of **every new active
vertex**. The new map may still be noninjective on its full
seam preimage away from those active boundaries.

Specialize `Active` to the B-exclusive target region in an
actual B-to-A selected-Q source flip: since Q maps into the
A/Left target side, the two active regions are disjoint and
the hypothesis that the inserted Q contributes no B-active
source vertex follows from target full-amalgam overlap.

This is a **one-step** universal boundary-injection preservation
principle, not an unconditional complete induction on geometric
Claim 2 states. The smaller-root mixed-piece selection and
zero-B-rank terminal exit remain separate. Verify the new
third named theorem via exact-head Lean CI.
