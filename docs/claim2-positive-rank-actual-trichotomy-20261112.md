# Track C: a concrete actual-step / smaller-root / seam-collision trichotomy

**12 November 2026. Draft awaiting exact-head Lean CI.** Full native
function-graph language; no source quotient or target-image counting.

## What is proved conditionally on the explicit input geometry

Take **any** actual finite connected forbidden full-native source
`Source`, its weak EHN map `f` into a true full free amalgam with a
common global canonical lift, and one genuine old geometric outer piece
`P` of positive width. Assume the full ordered root of P lies in
`S=f^{-1}(common seam)`, an A-exclusive source anchor a remains INSIDE
P's whole geometric piece, and the B-exclusive **SOURCE vertex count
inside the whole P** is positive.

The proposed theorem
`claim2_positiveRank_actualSuccessor_or_smallerRoot_or_seamCollision`
has **no original A-source support minimizer** and **no smallest
mixed outer-piece** hypothesis. It returns at least one of three
precisely typed alternatives:

1. An **actual full forbidden source replacement**, using ONE selected
   canonical Q, with genuine new geometric outer piece, original
   target-ordered outer-root coordinates, same original globally
   indexed canonical outer symbol, and strictly fewer B-only SOURCE
   vertices INSIDE the new actual outer piece.
2. An **actual smaller positive-width minimal closed separator** in
   the same old source. Its complete ordered root is strictly inside
   the B-only S-component's entire function-generated boundary T,
   remains inside S and P, and is exactly the opposite A-component's
   native generated boundary. The selected component may be MIXED.
   This is a source certificate, *not* a valid source flip.
3. `¬ Set.InjOn f S`: a literal weak-target root-image collision on
   the complete common-seam preimage. No injectivity property is
   silently inferred from the original root coordinates.

The proof branches on actual injectivity over S, then invokes the
merged arbitrary-closed-context positive-rank boundary dichotomy
(#894), deriving nonempty boundary from connectedness and actual
opposite separation from free-amalgam monochromaticity. In the partner
branch the merged #951 **actual** old-symbol geometric source flip
applies with T-injectivity restricted from S-injectivity.

## Mathematical significance and limits

The proof does not require A-support minimization at intermediate
states: that premise is therefore no longer part of the *local
trichotomy*. It does NOT eliminate the smaller-root or collision
alternative. It does not construct a valid successor in either
obstruction branch, nor automatically preserve the A-anchor through
an arbitrary state transition. It does not supply the all-target
exterior SOURCE-count invariant inside the first branch, since the
existing #951 result hides the detailed same-Q source gluing; for the
full iteration gate one still needs to integrate the already merged
#948 exterior-invariant API.

Consequently it does not instantiate `hPositiveStep` in #958,
nor prove original 2019 Claim 2 or its strong amalgamation endpoint.
This is intended as the **intermediate-state diagnostic** for
future root-repair or rank-profile arguments.

### Validation gate

One new Lean module and named `#print axioms` check, one registered
active root. Verify complete Lean build, permitted axioms and absence
of proof admissions on this exact branch SHA before merging.
Original manuscript remains frozen; no removed TODO is reinstated.
