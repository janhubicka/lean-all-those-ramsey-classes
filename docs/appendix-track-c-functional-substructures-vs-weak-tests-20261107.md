# Track C: actual functional substructures versus ambient weak tests (7 November 2026)

## Printed definitions examined

The survey's `main.tex` Definition `defn:locfin` (currently around lines 1071–1081) requires the completion of **every substructure** of a finite candidate on at most `n(B,C0)` vertices. With genuinely partial functions, a full substructure (the inclusion is a full embedding) is **closed under all defined function outputs** and reflects undefinedness; this is not an arbitrary weak vertex restriction. The auxiliary `ehn-functional-refinement.tex` explicitly says that substructures of functional structures are closed, and full embeddings preserve the whole function-value set.

The survey's separately displayed **weak substructure** convention clips each set-valued output to the chosen vertex set. The corrected complete OLD whole-mask `Option(Set)` encoding instead uses **whole-fibre deletion** when any output escapes the weak carrier. These two agree for at-most-singleton outputs (merged PR #747), but **not** for partly surviving multivalued outputs. Do not silently identify them.

The relational 2019 multiamalgamation local-completion axiom is yet another statement: in the tagged OLD language it tests all exact induced vertex sets of size at most `n`, including ones that are not `U`-closed. These *ambient* tests retain OLD domain masks even when the intrinsic whole-weak function domain becomes undefined. Its completion map need not be a full embedding of the intrinsic weak functional source.

## What the corrected (4b) source dictionary establishes

From merged PRs #747 and #902, corrected (4b) membership for all closed U-irreducible induced subtests plus U-closedness and positive primitive arities gives unique vertex part labels, complete OLD value and domain coherence, true decoded `Option(Set)` functions, and same-target ambient-to-positive functional completion transfers protecting canonical closed U-irreducible copies.

Draft PR #910 proposes the direct, **vertex-exact** dictionary for arbitrary (possibly U-reducible) candidate C:

```
(wholeMaskOriginalDecode C).IsClosed Q
  ↔ IsUSubstructure wholeMaskClosureRules C Q
  ↔ IsUClosed wholeMaskClosureRules (C.induce Q)
```

No generated hull is substituted for Q. The `IsUClosed.induce_iff_USubstructure` equivalence is already proved in the pinned 2019 partite library. The first equivalence derives by matching genuine decoded complete values to OLD complete-output tuples, then applying the existing 2019 relative closure lemma. All claims newly asserted in PR #910 remain **CI-pending**, until its proof and named axioms pass.

In particular, the **same cutoff n** indexes the two *families of closed exact carriers*: genuine functional full substructures of size ≤n versus tagged induced U-closed substructures of size ≤n. This does NOT identify their respective completion predicates, and does NOT equate them with the larger family of **all** ambient OLD-induced weak carriers.

## Correct interpretation of unary obstructions

The merged total-unary and fixed-point-free singleton regressions from PR #747 refute an attempted *per-test* equivalence between ambient relative OLD completions and **full embeddings of arbitrary nonclosed intrinsic whole-weak structures**. They also show a naïve all-weak-singleton-FULL local implication may be vacuous. **They are not counterexamples to the printed `defn:locfin`**, which only tests genuine functional substructures, and not to the complete corrected relational multiamalgamation theorem.

For single-valued unary F with `F(0)=1`, the singleton `{0}` is **not** a functional substructure, so a local-finiteness premise ranging only over genuine substructures does not test it. Its OLD ambient induced singleton is still a valid relational test, with an active OLD domain mask.

## Remaining genuinely open class-level step

To conclude the corrected relational (4c) local-completion axiom from a literal functional local-finiteness hypothesis ranging over closed original substructures, one still must handle the OLD ambient-induced tests that are **not U-closed**. The finite family of closed tests alone is not a pointwise replacement for the all-induced family. An independent argument using the published two-pass partite induction or a specifically strengthened local hypothesis may be needed. This is the core Track C open problem, not missing U-closed/functional compatibility for closed test carriers.

Other boundaries remain explicit: H isomorphism invariance, control-map assumptions, K(H) target membership, positive-input-arity/nullary branch, irreducibility of B when needed, and relative versus full map semantics. No strict native B-tree completion is inferred from source normalization alone.

This document is a research audit note. No frozen TeX prose or previously deleted author TODO has been changed.
