# Track B: actual A-free Q-certified B-descent has two source-support measures

15 November 2026. Stacked draft on #1248 → #1241 → #1237 → #1231.
The frozen original 2019 source manuscript and author-removed TODOs
are unchanged.

In earlier Track B #1231, the positive B-SOURCE-rank source-geometric
selector produced either an actual inner B-only piece or the two
literal old-root-capture/A-mixed obstructions. #1248 upgrades the
same-Q native state step to remember that the REMOVED OLD inner piece
was A-free, in addition to the literal selected forbidden Q, complete
Q+old-E native free diagram and the old/new E target agreement.

The new `Claim2AFreeSelectedQChainMonotonicity.lean` provides:

1. `claim2Native_positiveRank_AFreeQStep_or_capture_or_mixed`:
   the exact positive-B-rank dichotomy with a successful successor
   in this STRONGER one-sided Q-provenance relation. It invokes the
   same source-eligible inner piece and actual same-Q construction,
   without choosing another Q or source map.
2. `claim2NativeAFreeQChain_toProvenance` and
   `...preservesOriginalProfile`: every finite chain in the stronger
   relation projects to the earlier literal-Q relation while retaining
   original global selected piece symbol, ordered root-target
   coordinates, all exterior SOURCE-counts, and A-anchor target.
3. `claim2Native_AFreeQChain_reaches_zero_or_capture_or_mixed`:
   obstruction-sensitive finite descent in the stronger relation,
   so every nontrivial edge carries its OWN actual selected forbidden
   Q+E free-amalgam and old A-free component certificate.
4. `claim2NativeAFreeQStep_totalA_nondecreasing` and
   `...QChain_totalA_nondecreasing`: exact old/new native Q
   source-cost accounting implies TOTAL A-exclusive SOURCE support
   cannot decrease on any successful one-sided step or chain.
5. `claim2NativeAFreeQChain_globalBBudget`: the same chain
   satisfies `k + totalB(terminal) ≤ totalB(initial)` from exact
   exterior SOURCE-cardinality conservation and strict local B-rank
   descent. No weak target-image cardinality.

Therefore genuine one-sided selected-Q finite descent has two
separately meaningful source measures: A_total is nondecreasing
and B_total strictly decreases on each step. The A increase is
the exact PRIVATE Q-nonroot A-source cost from #1248.

**Mathematical caveat:** a globally original A-support-minimal
witness may cease to minimize A after the FIRST B→A replacement.
Even though selected symbols/exterior counts/root targets persist,
global original A-minimality cannot be reapplied at intermediate
states without a separate proof. A global initial (A,B)-lex minimum
actually forces strictly POSITIVE private Q A-source cost on any
successful one-sided B-decreasing step (#1248).
The remaining smaller-root capture and A-mixed obstructions are not
eliminated, and the root/boundary source-test initialization gates
still apply. The unrestricted original 2019 Claim 2/strong AP is
NOT claimed.

Named #print axioms/checks and protected source root added.
Keep DRAFT until exact-head full Lean, allowed axioms/no-admission,
import/source contract and inventory CI passes and parent stack
is integrated.
