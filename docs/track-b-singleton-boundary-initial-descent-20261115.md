# Track B: singleton complete generated B-boundaries

15 November 2026; stacked on original-minimizer trichotomy #1202
→ pairwise source-test #1199 → heterogeneous native descent #1158.

A full EHN weak map need not be globally injective. But if EVERY
complete function-generated boundary of a B-exclusive source
component lying in the chosen genuine outer piece contains at most
one SOURCE vertex, the weak map is trivially injected on that
boundary, regardless of collisions elsewhere in the source.

The new module `Claim2SingletonBoundaryInitialDescent.lean` gives:

- `Claim2NativePreBoundaryState.hasSubsingletonBActiveBoundaries`:
  explicit SOURCE-side at-most-one hypothesis, uniform over all
  B-active complete generated boundaries in the old geometric piece.
  No pairwise full irreducible-test cover is required.
- `boundaryInjected_of_subsingletonBoundaries`: proves exactly
  the original native `boundaryInjected` condition from that
  source-side hypothesis.
- `claim2NativePreBoundary_smallBoundaries_minimizer_reaches_obstruction`:
  for an original globally A-exclusive SOURCE-support-minimal
  forbidden EHN witness with already injected target outer root,
  the SAME initial source/map enters the full geometric finite
  B-SOURCE-rank descent and reaches old-root capture or A-mixedness.
  The original selected symbol, exact exterior SOURCE multiplicities
  for ALL target sets, root coordinates and anchor target are
  preserved with quantitative rank budget.
- `Claim2NativePreRootState.widthOne_rootTargetInjective`: under
  width one, target injection of the sole root coordinate is
  automatic, independently of collisions elsewhere.
- `claim2NativePreRoot_widthOne_smallBoundaries_minimizer_reaches_obstruction`:
  combines width-one automatic ordered root injection with small
  boundaries to initiate the original native descent WITHOUT
  ANY initial target-image or pairwise source-test coverage
  assumption.

**Critical scope:** neither geometric width one nor global
A-support minimality is asserted to force B-boundary source
subsingletonness. The hypothesis is genuine and explicit.
Nor does the conclusion eliminate old-root capture or
A-mixedness, prove a final root-collision repair or complete
unrestricted original Claim 2 / strong amalgamation. This is a
conditional special case and tests the exact initial-state API.

Protected active root and named #print axioms entries added.
New exact-head Lean build and import/contract/axiom/no-admission/
inventory CI required. Frozen 2019 manuscript unchanged; no
author-deleted TODOs restored.
