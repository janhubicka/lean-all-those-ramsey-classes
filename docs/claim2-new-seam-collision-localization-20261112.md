# Track C — exact locality of new seam collisions

**12 November 2026. New standalone draft; no CI certification yet.**

Suppose a genuine native full-functional selected-Q source flip has two
full structural embeddings of its unchanged complement E into Old and
New, literal full-complement target-map agreement, and a genuine full
native free-amalgam cover of the new source by the replacement side Q
and the retained complement E.

If the OLD weak map is injective on the complete old seam preimage,
two NEW complement-side source vertices mapping to the new target seam
cannot collapse: the same complement points represent old source
vertices with the same exact target images; old seam-injectivity and
the OLD FULL structural complement embedding's injection exclude them.

Thus any pair of DISTINCT new source vertices in the new target seam
which collapse under the NEW weak map includes at least one vertex:
(1) outside the full retained complement embedding and (2) inside
the replacement-side embedding. This is a literal SOURCE vertex,
not a quotient class or a distinct-target-image count.

The two new Lean declarations:
- `fullNativeReplacement_retainedComplement_seamInjective`
- `fullNativeReplacement_newSeamCollision_hits_replacementOutsideComplement`

This is a **collision localization**, not a collision elimination.
It neither proves the original seam injectivity nor that the new
replacement-side image is seam-injective. In the local trichotomy,
it should be used only after an explicit source flip under an old
seam-injectivity assumption. A future root-repair argument must
inspect newly inserted Q vertices, rather than the unchanged exterior.

Requires exact-head Lean compilation, named axiom checks, active-root
inventory and no-admissions audit. The 2019 numbered manuscript remains
frozen; no collaborator-removed TODO has been reintroduced.
