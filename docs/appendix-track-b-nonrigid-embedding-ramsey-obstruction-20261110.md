# Appendix Track B — full-embedding Ramsey obstruction from native symmetry

November 10, 2026. This is an **independent adversarial finite Lean regression** stacked only on the previously merged two-vertex irreducible-host regression #946. It does not modify the frozen survey manuscript.

## Mathematical obstruction

Take the empty original functional language (no relations or function symbols), a singleton vertex part, and the class K of **all** native finite structures. K is a genuine hereditary free-amalgamation class. Let A=B be the two-element native partite system from #946, with both vertices in the same part. In the original *unordered* language, B has a full part-preserving transposition automorphism `swapEmbedding`.

For an arbitrary finite candidate target C, choose a bijection from its vertex set to a finite linear order using `Fintype.equivFin`. Colour a **full native part-preserving embedding** e:A→C by whether the rank of e(0) is smaller than the rank of e(1). Then any full B-embedding f:B→C has both compositions f∘id and f∘swap as A-copies, and their colours differ. Hence C never witnesses the two-colour Ramsey arrow C→(B)^(A)_2.

This is the ordinary finite-structure rigidity obstruction to embedding-Ramsey. It is independent of the earlier **irreducible-host** obstruction and the corrected 2019 **ambient-relative local completion** axiom.

## Lean contracts

1. `swapEmbedding` is an actual full part-preserving native embedding transposing the two vertices and preserving all function fibres (vacuously).
2. `twoIsolated_no_fullEmbedding_RamseyArrow C` says **every** finite native partite target C fails the full native two-colour arrow for A=B=two isolated vertices.
3. `allNativeClass_not_fullEmbedding_partiteRamsey` says that even the class of all empty-language finite native structures, already proved a free-amalgamation class in #946, fails the *unordered* full-embedding `NativeKFinitePartiteRamsey2019` conclusion of the conditional Track B Ramsey descent #914.

Do **not** conclude that the merged #911/#914 conditional implications are logically invalid: they carry host/subclass and global local-completion hypotheses, and the earlier #946 counterexample already demonstrates those host hypotheses are inconsistent for this K. No unconditional Ramsey conclusion is claimed.

A future applicable general proof must use an appropriately rigid expansion and a correct transfer for its ordered embeddings, rather than simply forget the order. The class of all ordered structures is not itself closed under the ordinary native free amalgamation operation, so the input free-amalgamation class and ordered Ramsey expansion must be kept separate.

## Verification

Only additive Lean proof, named `#print axioms`, active-module-root and audit note. No new axioms, no admits/sorries, no changes to frozen English TeX, and no Lake revision change. The branch is draft until the exact-head full Lean build, source-integrity scan and named axiom checks pass.
