# Track C: selected inner B-active source vertex forces genuine geometric B-rank descent

13 November 2026. Additive to draft PR #1140 (stacked on #1134/#1132); full exact-head Lean/axiom CI pending.

## Genuine source geometry

The old complete complement of a true geometric minimal-separator
piece `inner` has carrier the literal complement of the selected
nonroot source component. Every vertex x of that component is
therefore absent from the image of the old full complement embedding.
The new lemma `geometricSelectedComponent_disjoint_fullOldComplementRange`
proves exactly this native source-carrier statement.

For an old outer geometric piece P with
`geometricPieceVertices Old inner ⊆ geometricPieceVertices Old P`,
suppose a genuine selected-Q replacement reconstructs an ACTUAL
new geometric outer piece with carrier Q plus retained E, identical
E target values, and no B-active Q source vertices. If a selected
inner-component source vertex x maps to the B-active region, then
`geometricSelectedInnerFlip_Bactive_card_strict` proves

```
Nat.card {w // w ∈ geometricPieceVertices New newOuter ∧ flip w ∈ BActive}
<
Nat.card {v // v ∈ geometricPieceVertices Old outer ∧ f v ∈ BActive}.
```

The hypothesis that an old B-active source vertex was deleted is
now **derived**, not assumed. The proof uses the exact #1140
counting theorem and the actual old complement's subtype carrier.

This is a direct simplification opportunity for the rank part of
in-flight same-selected-Q geometric successor #1120: once #1120 and
#1140 are integrated on a common checked head, its x/hvComponent/
hvRight, hCarrier, hQNoRight and hEAgree fields instantiate
the generic BActive theorem for the right-exclusive target region.
No new source witness is chosen and no weak-target injectivity
is inferred. Original forbidden family, profile and exterior
source-count invariants remain supplied by #1120.

The open mathematical gates remain selection after captured/mixed
smaller roots and the zero-B-rank A-clearing argument. Frozen
2019 paper unchanged; no collaborator TODO reinstated.
