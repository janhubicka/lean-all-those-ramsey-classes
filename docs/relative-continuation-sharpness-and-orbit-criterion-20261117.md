# Relative continuation types: sharpness and the finite-relational classification

Supplement to the 17 November 2026 proof note; English proof, not a Lean validation.

## Two distinct finiteness assertions

For every individual finite closed X, finite index of ~_{F,X} is NECESSARY and SUFFICIENT for a PRECOMPACT exact-shadow relation-only AP expansion, potentially using arbitrarily many symbols of a fixed arity across infinitely many nonisomorphic old roots. The sufficiency construction labels every closed subroot Y by its maximal continuation class; use one relation symbol for each ordered old-root type and allowed continuation class. Every FIXED finite old A has only finitely many closed subroots and finitely many labels on each.

If one also wants the manuscript's PARTICULAR format **finitely many new relations of each arity with support on distinct target coordinates only**, require the indices to be bounded uniformly over all n-vertex closed X. Then all root-specific classes can be assigned indices in {1,...,k(n)}, using only k(n) new n-ary relations. This uniformity is necessary for that diagonal-free finite-per-arity format. A merely finite-per-arity expansion allowing arbitrary high-arity diagonal coding can evade the uniform bound, so do not assert a broader necessity than proved.

For finite relational old L, there are only finitely many old n-vertex root types, hence pointwise finite index automatically implies uniform index. For infinite languages the distinction is real.

## Omega-categorical universal structures imply the uniform index

Assume L finite relational and K has an omega-categorical universal member U. For each finite full root X of cardinality n and each finite extension A>=X, let Omega_X(A) be the set of Aut(U)-orbits of embeddings e:X->U which extend to an embedding A->U.

For A,B>=X,

 A+_X B in K  iff  Omega_X(A) intersection Omega_X(B) != empty.

Forward: the finite allowed free amalgam embeds into U by universality, giving aligned embeddings. Reverse: choose embeddings of A and B into U whose root tuples lie in the same orbit; align them by an automorphism. Their union is a native EHN map from the actual free amalgam A+_X B into the allowed U (irreducible source tests stay inside one full side), so the free amalgam is allowed.

If o_n is the number of Aut(U)-orbits on n-tuples, every Omega_X(A) is a subset of a set of size at most o_n. Therefore each ~_{F,X} has index at most 2^o_n, UNIFORMLY in X.

Combined with the finite-continuation maximal-witness construction, this proves that for finite relational languages and a connected finite-forbidden-source class, uniform finite continuation index is EQUIVALENT to the existence of an omega-categorical universal member. This avoids using the old complement-regularity lemma, which is false under the semantic piece-equivalence patch.

## The intended examples

- F finite in any (possibly infinite) functional L: the finite source-cut table from the main proof gives the uniform bound without enumerating an infinite semantic upward closure.
- F infinite of all odd graph cycles: over an independent two-vertex root, the continuation types distinguish the two possible path parities and the disconnected case. Infinite raw path observations compress to finitely many continuation classes.
- The Gamma_m folded-root family proposed in draft PR #1264: the Boolean rooted contexts A_eta have pairwise different continuation sets because an opposite half for an index on which eta differs distinguishes them. Thus the index over the SAME singleton is at least 2^r for every r, excluding precompact AP expansion exactly as intended (conditional on complete validation of the original infinite family).
- HN19 CSS Section 4.4.2: the effective bounded forbidden family modulo the irreducible F1 is finite by the weak-order argument in the companion CSS note, hence the uniform bound holds; the local-completion/Ramsey proof is still independent.

## What does NOT follow

This does not assert the original distinct-source-root canonical lift is correct. It also does not repair the Ramsey theorem or old complement regularity by changing only ~_F. The expanded age here is genuinely constructed from finite maximal continuation classes. Its generic locally finite functional reduct is not claimed universal for nonlocally-finite countable native-function models.

Lean: fixed-X continuation rows, finite maxima, restriction to subroots, uniform coding, AP assembly, orbit necessity, and the finite CSS interface require source-matched kernel validation.
