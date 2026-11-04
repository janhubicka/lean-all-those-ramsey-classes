# Track C: eliminate arbitrary opposite y from the general-width source-boundary dichotomy

Stacked on PR #847, this module takes an **actual potentially noninjective** EHN map from a finite source to a genuine full native functional free amalgam, one genuine outer geometric piece P with its root within the complete target-root preimage S, a B-exclusive S-component B inside P, and a selected A-exclusive vertex a in the same P component, joined to x∈B by a source Gaifman path.

Let T=Cl(N(B)). The module derives T⊆S and, using the already validated monochromatic-component/separation theorem, constructs y **equal to a** outside T, genuinely in a distinct T-component. The source geometric dichotomy then supplies:

1. U=Cl(N(C_T(a)))=T: the entire generated opposite boundary is equal, so a matching partner exists for the conditional B→A flip (PR #829), subject to target-root injection.
2. U⊊T: the *exact* generated opposite boundary U is itself the root of a genuine **positive-width** minimal-closed-separator geometric piece with prescribed original source endpoints x and a; U⊆S∩P.

This removes the opposite-vertex/separation oracle from PR #847. It assumes **no intermediate A-support minimality**, no injectivity of the weak target map, no forbidden-source image quotient, and no hand-picked cutoff. It does NOT assert the smaller-root geometric piece is B-only, nor that the new transported outer context after a canonical flip is itself a minimal-cut piece. These are the genuine remaining positive-B-rank successor conditions.

Lean exact-head compilation and named axiom checks pending. The manuscript is frozen.

## From the actual local B-rank to a concrete selected vertex

`claim2_positiveLocalRightSupport_hasComponentVertex` proves that a strictly positive finite B-exclusive SOURCE count inside a genuine outer geometric piece P whose root lies in S necessarily supplies an actual x outside S in the selected nonroot component, mapped into the B-exclusive target side. No separate x-selection oracle, intermediate A-support minimality or global EHN injection is required. Combined with source connectedness and one A-exclusive outer vertex, the second theorem selects a and gives the partner/smaller-root dichotomy. General mixed smaller-root handling remains open.
