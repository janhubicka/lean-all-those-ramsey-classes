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
