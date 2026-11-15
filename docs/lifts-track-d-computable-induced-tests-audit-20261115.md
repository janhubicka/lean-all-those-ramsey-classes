# Correctness repairs to the finite counterexample certificate

## Classical enumeration was not executable

The first compilation repair replaced a nonexistent Finset.any with Finset.toList.any. This is still unsuitable for decide +kernel: Finset.toList uses classical choice (Multiset.toList/Quotient.out), rather than a specified computable enumeration. All three occurrences now use explicit List.finRange enumeration; the two quotient-edge searches use nested finite-range lists. No native_decide, axiom or admission was introduced.

## Irreducibility means the induced source structure

The old clique predicate used the full source's Gaifman adjacency even when testing a proper induced subset S. For ternary relations, an adjacency may be witnessed by a tuple using a vertex outside S. Such a tuple is absent from the induced structure. The revised adjacentWithin predicate requires ALL coordinates of a witnessing tuple to lie in S. Ambient adjacency is retained separately for paths in the original Gaifman graph after deleting a cut.

Concrete six-vertex regression: source ternary tuples are (0,1,3),(1,2,4),(0,2,5); red and blue relations are empty. The target adds (0,1,2). The identity is genuinely EHN: the actual irreducible source subsets are empty, the six singletons and the three original triple supports. None sees the new tuple. However {0,1,2} is an ambient Gaifman clique, so the old predicate incorrectly demanded reflection of the new target tuple there. The repaired predicate accepts the identity; two new decide +kernel declarations record the distinction.

An independent Python run checked all 64 subsets: 10 actual induced-irreducible tests versus 20 ambient cliques; the correct test accepts the identity, the old test rejects it. These are computational regressions, not a Lean kernel certificate.

The original C5 and both forbidden triangle sources have EMPTY ternary relations, so their actual irreducible subsets agree with their ambient Gaifman cliques. The correction therefore changes no intended counterexample claim, but makes the advertised generic finite table predicate faithful. Fresh exact-head Lean and named-axiom checks are still required.
