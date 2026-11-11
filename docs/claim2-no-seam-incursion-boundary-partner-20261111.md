# Track C: a seam-incursion criterion for the boundary-partner branch (11 November 2026)

**Status:** proposed Lean theorem in a draft branch. Exact-head Lean build,
allowed-axiom audit, no-admission scan, and protected-root inventory must all
pass before this can be called verified or merged.

## Setup

Take an original finite connected forbidden native functional source with
weak EHN map into a full free amalgam, a common FULL global canonical lift,
and an actual left-source-support minimizer. Let `S` be the entire
preimage of the common target seam. Let `P` be a genuine smallest
mixed old geometric piece, ordered by nonroot-component SOURCE vertex count.
Take a B-only seam component inside P, with generated boundary
`T = Cl(N(C_S(x))) ⊆ S`, and an actual A-only opposite vertex y
in P, considered after deleting T. Write
`U = Cl(N(C_T(y)))` for its complete opposite generated boundary.

Already merged:
`minimalLeftWitness_uncoveredInsideMinimalMixed_losesOldRoot`
proves that if `T ⊈ U`, the genuine smaller-root mixed
piece with geometric root `U ⊊ T` has a distinguished component
containing an actual old root vertex of P outside U.
Since the old root lies in S, any such failure creates
**a common-seam vertex internal to the smaller-root component**.

## New conditional consequence

Assume explicitly that every potential geometric piece with root
strictly inside T has a selected component containing **no** vertex of
the original entire seam S. Then the smaller-root alternative is
impossible: its verified old-root witness lies in S and in the
new selected component, contradicting the seam-cleanliness premise.
Thus `T ⊆ U`. Since U is always inside the closed cut T,
the complete opposite boundaries match, `U=T`.

The hypothesis deliberately restricts *source* seam incidence,
not weak target-image injectivity. The new theorem does not assert
that all smaller-root components enjoy seam-cleanliness. In fact,
the previously checked root-loss theorem identifies exactly how
they can fail to do so.

## Why this matters for the Claim 2 gap

This isolates the failure pattern needed for an unconditional
general-width successor. The missing lemma is now either:

- exclude seam incursion in the relevant chosen smaller-root chart,
  by an additional structural invariant, **or**
- handle the seam-incursion alternative without promoting a mixed
  selected component to a B-only flippable one.

The matched-boundary conclusion is conditional; a subsequent
right-to-left source flip still requires root-image injectivity
and the other hypotheses of the verified same-Q replacement
theorem. No global Claim 2 or strong amalgamation completion is
claimed. The numbered manuscript is frozen; no collaborator TODOs
have been reintroduced.

Lean theorem:
`minimalLeftWitness_noSeamIncursion_forces_matchingBoundary`.
Source: `AllThoseRamseyClasses/Lifts/Claim2NoSeamIncursionBoundaryPartner.lean`.
