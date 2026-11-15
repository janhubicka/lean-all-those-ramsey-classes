# Track B: initialize from pairwise irreducible source-test-covered root

**Stacked draft on Track B #1158.** Frozen 2019 manuscript unchanged.

The parent Track B branch proves a real original-minimizer initialization
alternative: a literal local B-generated-boundary SOURCE collision inside
the selected outer piece, or a finite native geometric descent reaching
old-root capture / A-mixedness. The parent requires injected ordered
outer-root target coordinates, not arbitrary source-wide injection.

The merged Track D theorem
`geometricRootImage_injective_of_pairwiseSourceTests` proves
exactly that ordered target-root injectivity when every pair of
distinct original separator-root SOURCE vertices belongs to a
common full irreducible source test; the containing test may include
vertices not in the root, so the induced root need not itself be
irreducible. This is a genuine strictly weaker sufficient condition
than requiring irreducibility of the whole closed root.

New `Claim2InitialPairwiseTestRootCover.lean` builds the SAME
`ForbiddenEHNWitness` as an initial `Claim2NativePreBoundaryState`,
using that checked theorem instead of assuming root image injection.
It then specializes the parent's actual minimizer
collision-or-reachable-obstruction theorem to this initial witness.

**No claims**: that arbitrary minimal geometric roots satisfy
pairwise test coverage; that initial B-active generated-boundary
collisions are impossible; that old-root capture/A-mixedness are
impossible; or that original Claim 2 / general strong AP is complete.

The module is an additive stacked DRAFT with named kernel axioms
and protected root; exact-head Lean and source/axiom/inventory
CI must pass before merging. Do not amend frozen TeX or reinstate
author-deleted TODOs.


## Source-side B-boundary coverage: a stronger conditional endpoint

The independent new module `Claim2PairwiseBoundaryCoverProgress.lean`
defines `Claim2NativePreBoundaryState.boundariesPairwiseCovered`:
every distinct pair in each actual complete generated B-active
boundary within the chosen old outer geometric SOURCE piece lies
in some genuine embedded FULL irreducible source test.

The already merged Track D theorem
`ehn_injOn_of_pairwiseIrreducibleSourceTestCover` converts this
explicit SOURCE-side condition into injection of the ORIGINAL EHN
map on each complete generated B-boundary. This is a theorem,
not an assumed global target/source injection.

Consequently
`claim2_pairwiseCoveredBoundaries_originalMinimizer_reaches_obstruction`
starts the **same** true native forbidden source state and applies
the checked minimizer/finite-geometric-descent theorem, producing
a finite chain with unchanged original symbol, ordered root target
coordinates, exterior SOURCE counts and A-anchor target, strict
B-source rank budget, and terminal OLD-ROOT CAPTURE or A-MIXEDNESS.

Together with the pairwise-covered ROOT construction, this provides
a fully explicit **source-test-certified sufficient scenario** for
both injection hypotheses in the Track B induction.

What remains: arbitrary forbidden geometric roots/boundaries need
not have these pairwise covers; the two smaller-root obstructions
are still not excluded. This does not establish original Claim 2,
strong amalgamation, or a general collision repair.

Separate named kernel-axiom checks and an active-root marker protect
the new theorem; this stacked PR remains DRAFT until its exact-head
full Lean, source-contract, inventory and axiom CI pass.
