# Original-global target relation: exact root-collision criterion

**12 November 2026. Draft until exact-head pinned Lean and axiom CI passes.**

For a real finite forbidden native functional source `A`, one actual
geometric source piece `d` of positive width, a target B, and an actual
weak EHN homomorphism-embedding `f : A → B`, there is an exact iff:

`original_global_relation_B(d.symbol, f ∘ d.roots)`
**iff** `Function.Injective (f ∘ d.roots)`.

The backward implication is already checked in
`geometricGlobalCanonicalRelation_of_weak`, and the forward
implication follows from
`globalFunctionalCanonicalRelation_injective`. Both address the
ORIGINAL globally indexed lift relation and the **same witness**, not a
folded replacement relation or a different candidate source.

This is a useful *criterion*, not a method of establishing injectivity.
If a genuine old outer root has collisions, exact preservation of the
source-global symbol and the target root coordinate tuple under
a selected-Q flip cannot imply the original target outer relation;
that relation is **false** at the colliding tuple. Such a case must
either be excluded by additional target hypotheses or handled by a
different construction. The existing #986/#994/#1006 source flips
make no unsupported global collision claim.

No numbered manuscript content is altered. No previously removed
collaborator TODOs are restored.
