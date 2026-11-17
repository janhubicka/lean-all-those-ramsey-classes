# Track D: all-m cyclic Gamma source geometry (17 November 2026)

The proposed infinite counterexample in draft #1264 uses the cyclic graph Γ_m on Z/(3m−1) with adjacency differences in [m,2m−1]. For integer representatives x,y in [0,3m−2], symmetry of the interval under d↦(3m−1)−d means this is equivalent to ordinary distance |x−y|∈[m,2m−1]. The module `TrackDCyclicThresholdArithmetic.lean` uses that transparent representation on natural numbers. A later native source structure restricts the predicate to the actual Fin(3m−1) vertex set.

Nine all-m Lean proof candidates establish symmetry, irreflexivity, triangle-freeness, the root R_m=N(0), root independence, private triangular E incidence E(a_j,b_k) iff k≤j, explicit three-edge paths 0→m→2m→d for short nonedges and 0→2m−1→m−1→d for long nonedges, and E-support for private D-chain arcs. All arithmetic is elementary linear inequalities and done by `omega`, with no finite m=3 enumeration or cardinal bound.

**This is not the entire cyclic family validation.** Remaining: formal identification of translated pairs with the zero-root path cases (or a direct nonedge three-path proof for arbitrary vertices), the vertex-connectivity/minimum separating-cut lower bound, the native source S_m assembly, the original image-closure test in the entire L-signature, the tagged original piece equivalence and the 2^r candidate root contexts. The positive general arbitrary-amalgam protected-half lemma and finite m=3 table theorem have passed and merged (#1269/#1273).

No manuscript edits. Exact-head Lean and named axiom CI must pass before kernel certification, and no counterexample to the full printed theorem is claimed formally at this intermediate step.

## Stronger all-pairs statement

The module now proves `cyclicThresholdEdge_ordered_nonedge_three_path`: every pair `x<y<3m−1` which is not an E edge has an explicit 3-edge path, with four exhaustive cases according to whether the two possible intermediate shifts wrap beyond `3m−1`. Its finite `Fin(3m−1)` counterpart `cyclicThresholdEdge_any_nonedge_three_path` handles the opposite vertex order by reversal and edge symmetry. All intermediate vertices are certified in range. Independent checks traversed EVERY nonadjacent pair for m=3,...,29 and all four witness cases passed.

This closes the native all-m source *graph* nonedge-path premise which the separate generic `noninjectiveWithThreePath_targetTriangle` proof uses (PR #1274). It still does not prove the full SOURCE family EHN printed image-closure assertion: the actual unary C/P/Q reflection, loop and D tables, T absence and native forbidden-triangle membership require explicit bridging.

## Compiler-driven boundary correction (17 November 2026)

GitHub Actions run 44032159409 correctly rejected the first nonedge-path proof. The four-case English geometry is sound, but the Lean witness expressions `x - m + 1` and `x - 2*m + 1` had **incorrect Nat truncated-subtraction semantics** at exact wrapping boundaries x=m−1 and x=2m−1: Lean evaluates `(x-m)+1`, not the intended integer x−m+1. Replaced them with `x+1-m` and `x+1-2*m`. Also replaced `all_goals unfold cyclicThresholdEdge` by `simp only [cyclicThresholdEdge]` so purely arithmetic range-bound subgoals do not cause an unfold failure. These fixes strengthen, not weaken, the required path-range and edge obligations. The new exact-head CI run must pass before the statements are kernel-certified.

Second CI triage: run 44032646888 rejected `simp only [cyclicThresholdEdge]` on pure numeric range goals because the simplifier made no progress. The edge formulas themselves and their four-case Nat-subtraction corrections survived. Each mixed goal now applies `try simp only [cyclicThresholdEdge]` before `omega`, avoiding any false requirement that an edge predicate occur in a numeric goal. This is a tactical repair; no statement, witness or hypothesis was changed. New exact-head CI pending.
