# Track B/D: new seam injectivity iff Q root reflection

**12 November 2026. Stacked on draft #1083.**
Original 2019 manuscript remains frozen; do not re-add removed TODO notes.

## Theorem and exact assumptions

`fullNativeReplacement_newSeamInj_iff_QrootReflection_of_local`
takes one genuinely native FULL free amalgam New = Q +_Root E,
the matching full old/new complement embeddings, a source weak
map f, a target weak map flip, and a Q-piece map gQ:Q→Left.
Assumptions:
* Old f injective only on the retained complement vertices
  mapping into the common target seam, NOT on all f-preimages.
* Full exact target agreement on the old/new complement E.
* Q-side factorization flip(iNewQ q)=jLeft(gQ q).
* The exact ORIGINAL common-root source/target coordinates:
  gQ(qRoot r)=iLeft r.

Under precisely those conditions the following are equivalent:
* flip is injective on the ENTIRE new target common-seam preimage;
* every q∈Q whose weak gQ image enters the target Left root
  was already a literal Q-root vertex.

The **forward** direction compares Q vertex q with the root
vertex qRoot r having the same Q-map image; new seam injection
forces them to coincide. The **reverse** direction uses the
complement-local source lemma #1083: Q root reflection forces
each new seam source vertex into E, where injectivity is retained.

`fullNativeReplacement_collision_forces_QrootReflectionFailure_of_local`
is a direct contrapositive producing a literal Q nonroot whose
gQ image belongs to the Left root whenever the new seam map
is not injective. It does not duplicate the full collision proof
and does not use a weak-image quotient.

## Why this is not unrestricted Claim 2

No source weak homomorphism-embedding is declared automatically
root-reflecting. In fact, the original canonical selected-Q
replacement does not currently provide this property. The theorem
is an EXACT characterization of what is missing to preserve
seam injection; it is not a construction of Q satisfying it,
nor an elimination of the smaller-root obstruction.
Weak target collisions elsewhere are allowed.

## Validation

The parent #1083 must merge first; then retarget to main.
Exact-head full Lean compilation, two named #print axioms,
permitted-axiom inventory, active-root/source/contract checks
and no-admissions scan must pass before this PR merges.
