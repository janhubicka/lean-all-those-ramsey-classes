# Track C: selected Q's no-B-exclusive property in the SAME new forbidden source

**13 November 2026. Independent source-level refactor; exact-head Lean CI pending.**
The numbered 2019 manuscript remains frozen.

The existing verified selected-Q contextual B-to-A flip proof already
constructs a target-Left factorization of the replacement Q and proves
`hNewPieceAvoid`:
```lean
∀ q : Q.Carrier, flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight
```
But its publicly exported theorem discarded this property when returning
the genuine selected Q/new forbidden source/weak target map and the
strictly falling B-SOURCE support inside the transported old outer context.

The strengthened endpoint
`geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile_andComplementAgreement_selected_withNoNewRight`
returns that no-new-B property together with:
- exactly the ORIGINAL selected Q and its canonical equivalence/profile;
- the full native new forbidden source and actual Q +_Root E embeddings;
- exact preservation of every unchanged E vertex's weak target coordinate;
- the function-closed transported outer context;
- the original ordered outer-root target coordinates;
- strict decrease of B-exclusive SOURCE count inside that context.

The older theorem name stays available as a *direct projection* of the
stronger one. The old proof implementation is not duplicated.
Both endpoints receive named `#print axioms` checks and the existing
protected active root remains unchanged.

This matters because the paired full-native source theorem in draft
#1101 and its B-specific specialization in draft #1113 can transport
all B-active generated-boundary injectivity ONLY if the SAME selected
replacement Q used for the strict B descent contributes no B-exclusive
vertices. A separately existentially chosen replacement is not enough.

Still required before a fully concrete Track C step theorem: propagate
this no-new-B certificate through the already validated actual new
outer geometric piece/anchor/exterior-support reconstruction (#1070)
without changing its selected-Q witness; then compose with the exact
active-boundary transfer. This new endpoint alone does not settle
the smaller-root mixed-component branch or the zero-rank terminal exit.

No weak-image quotient or distinct target-image counts are used,
and no removed collaborator TODO is reintroduced.
