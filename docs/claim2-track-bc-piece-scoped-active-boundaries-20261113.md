# Track B/C: piece-scoped active-boundary-injectivity transfer

**13 November 2026.** Proposed additive lemma stacked on the paired
boundary transport draft #1101. Original printed `ramsey.tex` is frozen.

## Why the scope matters

The exact-head verified and merged theorem
`claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective`
requires injection on the generated boundaries of B-only SOURCE
vertices belonging to the current **selected outer piece P**.

The generic #1101 transfer for ALL active source vertices assumes
injection for EVERY retained E-active vertex, including those
outside P. Its antecedent is therefore stronger than the input
of the actual two-branch positive-rank theorem.

This narrow lemma
`fullNativeReplacement_pieceScoped_activeBoundaryInj_transfer`
avoids silently strengthening the initial state invariant.
It receives two actual full native source free-amalgam diagrams
with the same retained source E, exact complement target-map
agreement, and an explicit pair OldPart/NewPart with the
carrier inclusion

```lean
NewPart ⊆ range iNewL ∪ iNewR '' (iOldR ⁻¹' OldPart)
```

It also assumes no new Q-side source maps into the target
Active region. For each B-active y inside NewPart, those two
conditions force y = iNewR e with iOldR e ∈ OldPart.

The OLD injection hypothesis is then used **only for that
old E-source vertex inside OldPart**, and the proved #1101
one-component boundary-transport theorem gives injection
on the entire generated boundary of y in New.

## Actual geometric instantiation still needed

For a genuine 2019 selected-Q outer flip, the exact constructed
new outer geometric carrier equals Q-new ∪ E(old outer
context). One must explicitly prove that the E context is
mapped from vertices of the OLD geometric outer piece and
that Q-new maps into the opposite Left target side.
Neither is inferred by this generic source-free-amalgam
lemma. Both are expected from the already merged actual
selected-Q carrier/weak-map certificates and draft
same-witness no-new-B PRs #1117/#1120.

This theorem DOES NOT supply the initial old piece's
active-boundary injectivity, a positive-rank successor in
the smaller-root branch, a target-root injective initial
witness, or the terminal minimizer contradiction. The
full-seam collisions can persist away from active boundaries.

## Validation

Draft until parent #1101 and this exact-head full Lean
project build, named permitted-axioms audit, active root,
source contracts and no-admission checks pass.
Do not re-add author-removed TODOs or edit numbered TeX.
