# Track D: infinite counterexample bridge, split into kernel-checkable obligations (17 November 2026)

The general protected-half obstruction and a fully explicit m=3 table regression were kernel-verified and merged in #1269 and #1273. English proof PR #1264 still supplies the unbounded cyclic Gamma_m family, the printed image-closure argument, and 2^r actual bouquet contexts. None of these three infinite ingredients is declared Lean-certified merely because the finite example passed.

Two independent native proof modules now isolate further universal pieces of that English argument:

1. **TrackDCollisionPathTriangle.lean**: EHN preservation of a binary E edge plus injectivity on that irreducible E-edge implies that folding the endpoints of any length-3 path produces an E triangle on three DISTINCT target vertices. Consequently, if every distinct nonedge has a source length-3 path, any collision produces a triangle. A separate native lemma proves that ORIGINAL tuple-surjectivity transfers emptiness of a ternary (or general arity) positive relation from source to target. These are exact source-map consequences, not a false assumption that arbitrary EHN maps are tuple-surjective.

2. **TrackDInfiniteRootProfileObstruction.lean**: the merged 2^r lower bound on candidate finite root profiles holds for every r under explicit 2^r original nonamalgamable rooted contexts. An elementary  n < 2^n lemma closes the numerical contradiction for any finite Profile. It does not assume or assert the existence of the actual cyclic bouquet contexts from the English PR.

**Remaining native work:** define Gamma_m and S_m as genuine native Structure values for all m; prove cyclic triangle-freeness, nonedge 3-path existence, connectivity lower bound and hence the original family regularity; check original D-chain/Start/End index rigidity and tuple-surjective image closure; package 2^r actual allowed pairwise nonamalgamable bouquets; finally link matching expanded root profiles to an allowed amalgam in a hypothetical precompact hereditary AP lift.

No new strong hypothesis has been substituted for the printed theorem. This is a source proof candidate, not a fully formalized counterexample. Exact-head Lean, named axiom, source-inventory and source-contract checks required. The numbered manuscript remains unchanged.
