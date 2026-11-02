# Appendix A / Track C — functional local-completion contract audit (2 November 2026)

## Non-negotiable theorem boundaries

The corrected 2019 theorem was proved in the relational **ambient OLD** language with proper full-root U-tags. In the genuinely partial partite functional setting let

- **C** be an arbitrary U-closed tagged relational candidate satisfying corrected clause (4b);
- **S** be the literal induced weak vertex subset (never the ambient closure hull);
- **A = wholeMaskOriginalDecode C** be the decoded genuine `Option(Set)` candidate;
- **H** be the original class of part-labelled genuinely partial functions.

Three independent existential assertions about a local test are involved:

1. **Ambient relative:** `HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S)`; an H-valued canonical tagged target with the corrected induced-closed U-homomorphism-embedding preserving persistent OLD domain masks.
2. **Intrinsic positive:** a true 2019 `IsOriginalPartialHomomorphism` of `wholeWeakInduce A S` into an H member; undefined inputs impose no constraints.
3. **Intrinsic full:** a FULL `PartialSetStructure.Embedding` of `wholeWeakInduce A S` into some H member; undefined inputs must remain undefined.

The fully axiom-audited source-data normalization at commit `a7c9ee586cd69a0818dd1982c48cff7ce94aa9f1` proves (1) ⇒ (2), with unchanged S, same map and same H target. Under corrected (4b), U-closedness and positive function arities it also derives a unique genuine vertex part, old-domain validity, canonical tag normality, entire complete-value coherence, and protection of canonical CLOSED U-irreducible test copies that embed into `C.induce S`. These facts do **not** make (1) imply (3).

### Explicit regression: ambient relative does not imply intrinsic full

The new `FunctionalWithParts2019TotalUnary*.lean` modules (latest CI pending) use a genuine two-point **total** unary H-member with `F(0)=some {1}`, `F(1)=some ∅`, and S={0}. Its exact tagged source is a finite canonical member of K(H), hence U-closed and corrected-(4b)-covered. Its ambient-induced OLD test has a relative H-completion back into the original two-point tagged source. But the intrinsic whole-fibre weak singleton has `F(0)=none`, so it admits NO full embedding into ANY H target; every H target has F everywhere defined. An additional lemma quantifies over **all S**, showing that the entire ambient-relative small-test family can hold while even one intrinsic full-weak small-test requirement fails. This compares **antecedents**, not the outer local axiom.

### Opposite regression: intrinsic full does not imply ambient relative (outside (4b))

The older all-undefined unary class H allows the intrinsic weak singleton to embed FULLY into H, while its retained ambient OLD active-domain record prevents a tagged positive map into **any** H target. This individual counterexample does not satisfy the stronger corrected (4b) source-side H-coverage, and must NOT be reported as a class-level theorem refutation.

### Why the full-intrinsic-weak class-local axiom may be vacuous

The proposed `FunctionalWithParts2019IntrinsicSingletonVacuity.lean` shows formally: if no one-point whole-weak test of any candidate can FULLY embed into H, then a candidate whose every exact weak subset of size ≤1 has a full H-completion must have **empty carrier**. Hence the corresponding candidate-level fixed-cutoff local-completion implication holds for all B∈K(H) and C0, independently of control/coverage, by the trivial empty-source copywise completion.

The proposed `FunctionalWithParts2019FixedPointFreeSingleton.lean` exhibits a NONEMPTY original partial-unary H class with this property: each F(x) is a defined singleton {y} with y≠x. Two-point swaps are H members; true function-closed H-substructures remain in H. No one-vertex whole-weak source fully embeds into any such member. These recent new proofs are **CI pending**, not green at the time this note was created.

This does **not** establish the class has the remaining strong amalgamation and ordered irreducible Ramsey-ambient hypotheses, nor that it is a non-Ramsey counterexample. It establishes the logical weakness of the local premise, which can be trivially satisfied in nonempty natural functional classes.

## Exact class-level implications currently proved

The verified `FunctionalWithParts2019CorrectedIntrinsicLocalTransfer.lean` gives:

`GenuinePartiteIntrinsicCanonicalProtectedLocalCompletionAt H B C0 n` ⇒
`GenuinePartiteTagged2019LocalCompletionAt H B C0 n`

at the **same n**. Its native H-valued completions preserve source-defined whole function fibres, actual vertex parts and full embeddings on ambient canonical closed U-irreducible protected tests. It then yields the full genuine part-preserving H Ramsey theorem under the explicit hereditary, strong-amalgamation, isomorphism-closure, positive-arity, ambient Ramsey and inclusion hypotheses.

This is a **corrected sufficient local class hypothesis**, not the literal naive native-full-weak assertion. Neither theorem assumes strict full-functional B-tree sparsening or a total-fibre-reflecting global projection.

## Remaining decisions / TODO for authors

1. Choose whether the manuscript means ambient OLD-induced weak completion, corrected source-defined functional completion protecting ambient canonical closed copies, or full intrinsic weak completion. They cannot be treated as synonyms.
2. If the intended original hypothesis is the last, a *new class-level argument* is needed: merely applying the ambient corrected 2019 theorem is logically invalid because its all-small-test antecedent need not imply all-small-test intrinsic full completability.
3. To prove an original-theorem implication, identify a stronger relevant class invariant guaranteeing that pointwise ambient certificates imply the original native completion *or* find a different proof that uses the full-intrinsic local axiom directly. A general transfer is false by the total-unary exact test.
4. Continue to treat positive-output nullary functions, strict native functional B-trees, total-fibre-surjective maps, and original-versus-whole-fibre/clipped weak restriction as separate theorem contracts.
5. This research track may edit new Lean modules and its own Markdown notes only. No changes to frozen manuscript prose, no reintroduction of deleted TODOs, and no green marker for unverified recent modules.

CI baseline for latest pending finite and vacuity modules: [Track C PR #747](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/747). The last known fully green baseline is [run #41303169829](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/41303169829).
