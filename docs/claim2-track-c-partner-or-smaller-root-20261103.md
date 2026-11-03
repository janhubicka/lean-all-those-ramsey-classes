# Claim 2 — the uncovered generated-boundary branch without A-minimality

For an actual geometric outer piece `P=R∪C`, an arbitrary closed cut `S⊇R` and an `S`-component `B` based in C, set `T=Cl(N(B))⊆S∩P`. For any opposite vertex y in another `T`-component, let `U=Cl(N(C_T(y)))⊆T`. The new native theorem `geometricInnerBoundary_partner_or_smallerRoot` proves the **exhaustive** alternative:

- `U=T`: the opposite component is a genuine *partner* with the entire generated root T, exactly the missing geometric hypothesis of the partner-based contextual flip (PR #829).
- `U⊂T`: the exact smaller generated boundary U is already a **minimal closed separator**, and therefore (on a finite carrier) the complete ordered root set of a genuine new geometric source piece, `root(d)=U⊂T⊆S∩P`, whose distinguished left/right vertices are the chosen original x,y.

Proof basis: `componentBoundaryClosure_preserves_exact_component`, `oppositeBoundaryClosure_isMinimalClosedSeparator`, `finiteMinimalClosedSeparator_toGeometricChart`, and the Track C localization theorem merged as #824.

This theorem does NOT silently promote the smaller-root piece to a B-only piece. Shrinking the cut may enlarge its selected component and add A-only vertices. The iterated original-2019 Claim 2 proof still needs a controlled response to this **uncovered boundary** branch. It also needs root-target injection and genuine outer-piece reconstruction after a flip, not derivable from an all-test closed-context profile alone.

No intermediate A-support minimality, weak-image quotient, connectedness assumption beyond actual selected components, or change to frozen manuscript prose. Named Lean axiom audit, one active proof root, exact-head CI required.
