# Track C — EXACT additive SOURCE support cost of a selected-Q replacement

15 November 2026. Stacked on #1204. Exact-head full Lean,
permitted-axiom, no-admission and protected-root CI pending.
Frozen numbered 2019 manuscript left unchanged.

The generic full native Q+_R E source glue has literal SOURCE
covering and exact Q/E overlap on the complete root R. PR #1204
proves the new A-active SOURCE set is the disjoint union of
(1) retained E-image A-active vertices and
(2) inserted Q-NONROOT-image A-active vertices.
This new file applies finite set cardinal arithmetic
(Set.ncard_union_eq, Set.ncard_image_of_injective) to obtain
the exact ADDITIVE Nat.card formula:

  new total A-active SOURCE support
    = retained E A-active SOURCE support
      + private Q-nonroot A-active SOURCE support.

The old full native complement E is an actual subtype of the
original source excluding exactly the removed selected inner
component, and the old/new E weak-map target coordinates agree
on every vertex. Therefore no A-active OLD SOURCE vertex can
be deleted when the removed old selected component is A-FREE;
the old A-support set is the old E-image of the same source
E-subtype as above. This yields the exact genuine geometric
selected-Q support cost:

  Nat.card {w // flip w ∈ Active}
    = Nat.card {v // f v ∈ Active}
    + Nat.card {q // q outside Q.root ∧ flip (iQ q) ∈ Active}.

No old-source finiteness is needed in the old-E equality;
finiteness of the NEW source is explicit for the additive
cardinal arithmetic. All counts are of ACTUAL SOURCE vertices,
not weak target-image sets, and iQ/iE are genuine full native
embeddings (the weak target map is not assumed injective).

This precisely quantifies the original A-support change along
a B-to-A selected-Q flip: every newly inserted A-exclusive
private Q source vertex contributes one unit. The formula
is stronger than the qualitative strict-increase and iff
A-neutrality tests in draft #1196.

The next genuine research problem is to find an eligible
B-decreasing Q selection with zero such A-cost, or a new
well-founded potential that tolerates positive A-cost. This
module does NOT solve Q selection, the split-root capture case
or the general original 2019 strong amalgamation argument.

Four named #print axioms and one protected active root.
No collaborator-removed TODOs have been reinstated.
