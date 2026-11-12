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
