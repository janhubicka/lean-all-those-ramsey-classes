# Published 2019 statements and their exact Lean status

The library formalizes actual relational structures with the
2019 closure-description language. The original printed Theorem 2.18
is refuted; the **coordinated corrected** theorem is proved. These
are mathematically different claims.

| Paper claim | Formal entry point | Verdict |
| --- | --- | --- |
| Definitions 2.12–2.13, closure and roots | `ClosureRule`, `ClosureDescription`, `IsUClosed` | Matched definitions |
| Intrinsic U-irreducibility | `IsUIrreducible` | Matched definition; not ordinary irreducibility |
| Literal Definition 2.15 map | `IsUHomomorphismEmbedding` | Refuted universal-theorem context |
| Corrected map | `IsInducedClosedUHomomorphismEmbedding` | Protected induced tests BOTH U-closed and U-irreducible |
| Definition 2.17 class axioms | `InducedClosed2019MultiamalgamationClass` | Corrected (4b); original weak (4c) |
| **Literal** Theorem 2.18 | `Theorem218Counterexample.lean` | **False**, Lean counterexample |
| **Corrected** Theorem 2.18 | `coordinated2019_theorem218` | **Proved**, unrestricted |
| Theorem 2.19 finite partial functions | `allThoseRamseyClasses_theorem_2_19_partialFunctions` | **Proved** in pinned dependency |
| Lemma 2.23(1), exact closed subsets | `lemma_2_23_one` | Proved |
| Lemma 2.23(2), free amalgams | `IsFreeAmalgam.isUClosed` | Proved with closed common root |
| Lemma 2.28, repaired Picture coverage | `lemma_2_28_coordinated_unrestricted_induced` | Proved |
| Lemma 2.29, repaired coverage | `lemma_2_29_coordinated_induced_full` | Proved; literal stronger assertion false |
| Lemma 2.30 original rank induction | native `InducedClosed2019*` modules | **Unfinished original proof**, not needed by alternative theorem |
| Ordered posets with linear extension | `orderedPoset_isRamsey` | **Proved**, equivalent named strict-order encoding |
| Freely ordered partial Steiner triples | `Steiner*` application modules | Only components; final Ramsey theorem open |
| Metric, pointed, unary, interposition, incidence | manuscript applications ledger | Full class conclusions still open |

## What the corrected Theorem 2.18 actually assumes

Fix the original B in K and C0 in the ambient Ramsey class R,
then select the same n(B,C0) for all candidates C.
The protected positive maps are embeddings on exact induced tests
that are **both U-closed and U-irreducible**. Clause (4b) uses
exactly those closed irreducible tests. Clause (4c) retains **every
original weak induced set S with |S| <= n**, even when S is
nonclosed. Neither the tested S nor C0 is replaced by its U-hull.

These are two simultaneous changes: modifying only (4b), without
the map predicate, still admits the checked paired-equivalence
obstruction. Restricting protected tests weakens the map predicate,
so it **strengthens** the local-completion implication (its
antecedent becomes easier). A raw Lean class predicate is not
automatically invariant under isomorphism; the coordinated class
interface explicitly includes that condition.

`coordinated2019_theorem218` is a proved proposition packaging
the general Ramsey-class conclusion, not a conditional native-rank
constructor. The actual source proof is
[Coordinated2019ProfileSparseWitness.lean](../../AllThoseRamseyClasses/Published/Coordinated2019ProfileSparseWitness.lean)
and passed [full CI 38479503776](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38479503776).

## Original proof and corrected conclusion differ

The finite generated-closure profile/sparsening proof gives the
coordinated theorem for ANY chosen finite weak-test cutoff, with
no closedness assumption on original C0. It does NOT formalize
the old rank-increment argument of Lemma 2.30. Keep its orange
review marks independent of the green corrected theorem.

The ordered-poset instance was fully discharged by PR
[#227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227),
[CI 38633955517](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38633955517),
merged `01e890503a86b0e413f8b0ffb0a763dd7db42020`.
The proof uses strict vertex order, reflexive partial order
and an inert third empty relation, rather than silently asserting
identical Lean language symbols with the paper.
