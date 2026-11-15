# Track D — native connectedness bridge for the replacement family (15 November 2026)

The repaired presentation is G = FullRangeEHNSaturation F; it contains all vertex-surjective EHN images of finite original forbidden structures, including extra target positive incidences. It is NOT the original tuple-surjective generated weak quotient.

The new `FullRangeSaturationConnected.lean` module establishes (subject to exact-head Lean CI):

* If A is nonempty and its complete native Gaifman graph is connected, then every vertex-surjective EHN image B is nonempty and connected. Each original adjacency maps either to equality or a target adjacency, by the already verified `weakFunctionalGaifmanAdjacent_map`, and transitive paths push forward.
* `GlobalForbiddenSourcesConnectedNonempty F` implies `GlobalForbiddenSourcesConnectedNonempty (FullRangeEHNSaturation F)`. The argument works for native set-valued function symbols: positive input/output incidences appear in the Gaifman projection.
* In a positive-arity native language, the existing connected-family JEP theorem therefore applies to the saturated forbidden-free shadow class. Its old shadow also agrees with the original forbidden-free class by the parent PR's avoidance equivalence.

**No new arbitrary-range-closedness assumption** is being inserted. The JEP transfer and connectedness are independent of the relational full-image-normal-form proof.

The module is STACKED on parent draft PR #1228 and must not be merged before both exact-head full Lean/axiom/source/inventory CI gates pass. It proves neither geometric-piece regularity for unbounded infinite forbidden families, nor the missing Track C Claim 2 iteration or the printed unrestricted original maximal-lift lemma. The numbered manuscript remains frozen and collaborator-removed TODOs stay removed.
