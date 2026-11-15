# Bounded forbidden-source size implies a global minimal-cut root-width cutoff

This independently useful result is for the GENUINE 2019 global piece-setoid on actual selected minimal-cut pieces. It neither changes the forbidden family nor invokes a folded all-closed-component expansion.

**Source statement:** If every forbidden source A satisfies Nat.card(A) ≤ N, then every selected forbidden piece of width n has n ≤ N. The separator is enumerated by an injective map Fin n → original source carrier, so this is an immediate cardinality inequality. Consequently, for n > N, the type of global piece equivalence classes is EMPTY and hence finite; all global added relation symbols have arity ≤ N.

This isolates a concrete formerly implicit step in the finite-family saturation repair: full-range EHN saturation preserves any uniform source size bound, so the repaired finite relational presentation has NO extra symbols at widths exceeding that bound. **It does not yet prove regularity:** the remaining task is to prove finiteness of the actual global quotient classes at each width 1≤n≤N using the finitely many FULL isomorphism representatives and root-preserving transport of genuine selected geometric pieces.

A naive inference from finite representative structures to finite global quotient charts is insufficient because each actual forbidden piece is defined only up to a root-preserving full isomorphism, and minimal closed separators must be transported between source carriers. The missing geometric transport lemma is not inserted as an axiom.

New Lean module `BoundedForbiddenRootWidth.lean` with four named axiom checks and active-root registration; source code pending exact-head all-module build, named axiom, integrity and inventory checks. Independent branch based on main; does not merge or alter frozen numbered manuscript.