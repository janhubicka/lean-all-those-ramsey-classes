# Track C: no escape from retained private complement for ANY root-containing cut

**12 November 2026. Standalone native-source proof draft; exact-head CI pending.**

Let Whole = Left +_Root Right be an actual FULL functional free
amalgam, including all original relations and complete set-valued
function fibres. Let S be ANY subset of Whole that contains every
vertex of the embedded shared source Root. S is NOT required to
contain the entire inserted Left side, to be function-closed,
or to be a target-root-preimage.

Choose a retained Right vertex x whose source image avoids S.
Write SR = iRight⁻¹(S), and Private = Right\\SR.

### First theorem

`fullFreeAmalgam_private_component_stays_right_of_rootCut`

The complete connected component of x in the true Whole
Gaifman graph after deleting S is contained in the image of
the retained private Right subset.

Reason: the already-validated full-native
`fullFreeAmalgam_rightPrivate_neighborhood_eq_image`
identifies the neighbourhood of the ENTIRE embedded
Right\\SR set with the embedded Right neighbourhood.
Since the latter neighbours lie in SR, every external
Gaifman neighbour of this private Right set belongs to S.
No path avoiding S can leave it, by the checked
`reachOutside_stays_in_avoid_boundary`.

### Second theorem

`fullFreeAmalgam_private_component_generatedBoundary_in_right_of_rootCut`

The WHOLE function-generated external neighbourhood
boundary of that selected S-avoiding component also lies
inside the full embedded Right complement.
The component equals the embedded inverse-image subset
CE of Right, which is PRIVATE to SR. The verified
`fullFreeAmalgam_private_generatedBoundary_eq_image`
then gives exact boundary-image equality.

No weak EHN source map, source finite cardinality,
global source injectivity, target-image quotient,
forbidden-family minimizer or canonical-lift
assumption occurs.

### Significance for Claim 2

Unlike the older private-component results whose cut includes
the ENTIRE replacement Q, these theorems apply to an ARBITRARY
cut containing only the actual shared root. In particular
they can apply to the preimage of the TARGET common seam even
when some inserted Q-nonroot vertices also map into it.

This is the missing preliminary path-confinement step for
a repeated active-B-boundary injection invariant: private
retained components cannot acquire new Q-only neighbours,
regardless of new global seam-image collisions.

The next step is to identify corresponding E-private
components between two actual full source diagrams and
transport their exact generated boundaries with the already
verified pair theorem. This draft alone does NOT prove
that entire iteration or eliminate the smaller-root mixed
case. Original 2019 manuscript is frozen.


## Stronger exact boundary transport (12 November continuation)

Two additional Lean theorems strengthen the initial mere-confinement
results, without adding assumptions:

- `fullFreeAmalgam_private_component_eq_image_of_rootCut` identifies the
  ENTIRE S-avoiding component based at a retained Right vertex with
  the full Right embedding's image of the exact component after
  deleting `SR = iRight⁻¹(S)`. This uses full-private Gaifman
  neighbourhood equality to seal the embedded Right component from
  the inserted side, and full native edge reflection to transport
  each Right-internal path into the whole structure.
- `fullFreeAmalgam_private_component_generatedBoundary_eq_image_of_rootCut`
  consequently identifies the ENTIRE function-generated external
  boundary with the image of the exact corresponding Right-side
  boundary. It uses the already verified full-native
  generated-boundary-image lemma and handles all function fibres.

Unlike a cut deleting the whole Left/Q piece, S can be the
preimage of the TARGET common root, so this equality is the
missing source-geometric bridge for identifying B-active boundaries
as *retained-complement boundaries*. Both stronger declarations
have independent `#print axioms` checks. **Pending exact-head Lean CI**.

Still required: exact matching of the retained-side seam cuts across
two successive selected-Q source maps, and management of mixed
smaller-root states; the lemma alone gives no infinite iteration.
