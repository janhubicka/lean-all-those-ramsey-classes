# Track D: all-m cyclic Gamma source geometry (17 November 2026)

The proposed infinite counterexample in draft #1264 uses the cyclic graph Γ_m on Z/(3m−1) with adjacency differences in [m,2m−1]. For integer representatives x,y in [0,3m−2], symmetry of the interval under d↦(3m−1)−d means this is equivalent to ordinary distance |x−y|∈[m,2m−1]. The module `TrackDCyclicThresholdArithmetic.lean` uses that transparent representation on natural numbers. A later native source structure restricts the predicate to the actual Fin(3m−1) vertex set.

Nine all-m Lean proof candidates establish symmetry, irreflexivity, triangle-freeness, the root R_m=N(0), root independence, private triangular E incidence E(a_j,b_k) iff k≤j, explicit three-edge paths 0→m→2m→d for short nonedges and 0→2m−1→m−1→d for long nonedges, and E-support for private D-chain arcs. All arithmetic is elementary linear inequalities and done by `omega`, with no finite m=3 enumeration or cardinal bound.

**This is not the entire cyclic family validation.** Remaining: formal identification of translated pairs with the zero-root path cases (or a direct nonedge three-path proof for arbitrary vertices), the vertex-connectivity/minimum separating-cut lower bound, the native source S_m assembly, the original image-closure test in the entire L-signature, the tagged original piece equivalence and the 2^r candidate root contexts. The positive general arbitrary-amalgam protected-half lemma and finite m=3 table theorem have passed and merged (#1269/#1273).

No manuscript edits. Exact-head Lean and named axiom CI must pass before kernel certification, and no counterexample to the full printed theorem is claimed formally at this intermediate step.
