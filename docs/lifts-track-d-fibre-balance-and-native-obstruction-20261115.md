# Track D — exact native source-seam fibre audit (15 November 2026)

This note concerns the original 2019 Section 3 native functional semantics, using genuine EHN maps of ORIGINAL forbidden sources. The numbered manuscript remains frozen, collaborator-deleted TODOs are not restored, and no unrestricted original Claim 1/2, strong AP or Ramsey assertion follows.

**Verification status:** parent draft PR #1194 must pass its independent exact-head Lean and axiom checks before stacked draft PR #1205 can be merged. All new declarations in #1205 are at present CI-pending. Their source proofs should be treated as proposed until full build, permitted axioms, source/import/Section 3 contracts, active-root inventory and no-admissions checks have passed.

## General exact finite balance

For finite original source vertex set V, map f:V→T and actual target seam X⊆T, define

\[
C_X(f)=|\{(u,v)\in V^2:u\ne v,\ f(u)=f(v)\in X\}|.
\]

Move one original source vertex a from s=f(a)∈X to a distinct t∈X, leaving every other source image unchanged. If k_s and k_t are sizes of the FULL ORIGINAL SOURCE fibres f⁻¹(s) and f⁻¹(t), respectively, then

\[
C_X(g)+2(k_s-1)=C_X(f)+2k_t.
\]

Exactly 2(k_s-1) ordered collision pairs are removed (the two orientations involving a and each other source vertex in the old s-fibre); exactly 2k_t are created (the two orientations involving a and each old t-fibre source vertex). All pairs not incident with a remain unchanged. Thus

\[
C_X(g)<C_X(f)\quad\Longleftrightarrow\quad k_t<k_s-1
\quad\Longleftrightarrow\quad k_s\ge k_t+2.
\]

New modules in stacked PR #1205 contain exact pointwise created/removed collision-pair equivalences, cardinality of the two ordered orientations, gained/lost finite pair-set equalities, the subtraction-free cardinal identity, strict-drop iff, and the bridge from Finset cardinal to precisely the Nat.card subtype invariant in the merged original forbidden EHN witness.

## New conditional genuine native EHN obstruction

For a genuine forbidden original EHN witness w selected lexicographically (first by number of ORIGINAL source vertices mapped left-exclusively, then by number of ordered distinct ORIGINAL source pairs collapsed inside the actual common seam), a same-source recolouring a:s→t with full source-fibre imbalance k_s≥k_t+2 cannot itself be an EHN map. Its original left-exclusive source support would remain unchanged and its genuine secondary pair count would strictly decrease, contradicting the actual minimizer.

This removes the global-unused-target-point requirement of the older conditional source split in #1163. The destination t may already be occupied by other original source vertices.

Crucially, the conclusion is NEGATIVE: the proposed recolouring is not EHN. By merged #1176 it has an actual LOCAL old-language failure: a positive old relation, a native set-valued function incidence involving the changed source coordinate as input or output, or a FULL irreducible source test. No successful recolouring or full source-image quotient is constructed. Source-side geometric profiles and strict left-support descent remain untouched.

## Adversarial blockers retained

- Balanced original source seam fibres can already minimize the full collision count, even while selected geometric source roots collapse. Parent #1194 gives a globally minimal three-to-two example.
- A selected minimal function-closed separator may discard the input coordinates of an unliftable original relation/function incidence. A saturated hull is not an automatically flippable forbidden piece.
- The original canonical piece-class relation vanishes on collided root tuples. Common original maximal-lift profile agreement does not create positive added predicates at such tuples.
- Pairwise joint irreducible FULL source tests ensure root injectivity conditionally (merged #1190); connectedness and minimal closed separator selection do not yield that coverage in general.
- The exact printed tuple-surjective forbidden-image closure must never be replaced with vertex-surjective weak quotient/full-image closure; the merged five-cycle counterexample is still relevant.

## Critical next task

Stop extending the numerical secondary-invariant machinery unless a concrete use in a source-profile-preserving replacement emerges. Return to the ORIGINAL maximal-common-lift/selected forbidden-geometric-piece step: either exclude uncovered colliding roots using the actual old-language maximality hypotheses, or construct a genuine EHN replacement/flip preserving the selected piece, full root compatibility and STRICTLY decreasing original left-exclusive SOURCE support. Track C's subsequent positive-rank descent is an additional independent gate.
