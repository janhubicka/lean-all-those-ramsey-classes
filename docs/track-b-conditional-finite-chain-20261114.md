# Track B: conditional finite selected-Q iteration (14 November 2026)

New module: `AllThoseRamseyClasses/Lifts/Claim2ConditionalFiniteChain.lean`.

The module formalizes the **logical iteration kernel** independently of any geometric selected-Q construction:

- `ConditionalSelectedQChain step n s t` records **n actually supplied** steps, not arbitrary possible replacements.
- `conditionalSelectedQChain_preserves` transfers any state invariant preserved by every individual step through an entire finite chain.
- `conditionalSelectedQChain_length_le_rank` bounds chain length by the initial **literal SOURCE B-rank** whenever each actual step strictly decreases rank.
- `conditionalSelectedQChain_zero_rank_only_empty` excludes positive-length descent from rank zero.

This is an intentionally small, honest theorem interface: apply it to one-step output of `geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorRootAndBoundaryInj` only **after** defining a genuine state type and relation whose fields include the original global symbol, exact exterior SOURCE counts, root-target injectivity, B-active boundary injection, and an A-only source anchor.

## Not discharged

The original initial minimizer is not shown to satisfy B-boundary injectivity; eligible one-sided selected-Q steps are not shown to exist for every positive rank. Smaller-root old-root capture/A-mixed alternatives are unresolved. No terminal zero-B-rank contradiction for the original Claim 2 is derived. Thus these new lemmas are **conditional iteration**, not a completed unrestricted Claim 2.

The frozen numbered 2019 manuscript and collaborator-removed TODOs are unchanged. The new module needs exact-head Lean CI and axiom/admission audits before merging.
