# Appendix A / Track C — post-merge theorem ledger (6 November 2026)

## Verified baseline

Merged [upstream Lean PR #747](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/747), CI [run #41852934761](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/41852934761) **green**, including theorem axiom checks. This is now part of `main`.

For any tagged relational candidate `C` which is U-closed and has corrected (4b) coverage by the canonical image K(H) of genuine part-labelled Option(Set) functions, with positive primitive function arities, Lean proves:

1. Every vertex carries **exactly one actual unary part relation**. The part assignment is reconstructed; no arbitrary auxiliary part map is assumed.
2. Every ordinary irreducible exact induced weak support embeds into **some** canonical genuine H-member. The H-member may depend on the support; no fixed B-copy coverage is required.
3. OLD complete graph witnesses have valid domain masks, active domain roots are injective, active domain masks have complete values (including **defined-empty**), full-root closure tags are canonical, and output values are coherent across equality patterns.
4. The independently partial OLD decoder is defined **iff** the ambient OLD domain predicate is active. It distinguishes `none` from `some empty`. Recovered function outputs are transversal to the recovered vertex parts.
5. Any genuine H-valued ambient-relative local completion on **exactly S** gives a same-target, same-map original source-defined functional local completion, preserving vertex parts and **canonical closed U-irreducible copies that embed in the ambient OLD exact test**.
6. The corrected native *canonical-protected* local-class axiom is sufficient for the published corrected ambient local axiom, at the same cutoff, and hence for the genuine part-preserving functional Ramsey theorem under its other explicit original class assumptions.

These are established by the `FunctionalWithParts2019Corrected*` and `FunctionalWithParts2019RelativeProtectedBridge` modules from the merged PR.

## New isolated PR #902 — verification pending

[Follow-up PR #902](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/902) contains **proposed** convenience and recovery endpoints (do not mark green before CI):

- `FunctionalWithParts2019CorrectedSourceCertificate.lean` puts all consequences (1–5) above into one reusable Lean structure and exposes the transversality/domain equivalence **in the ORIGINAL genuinely partial functional language**, not merely the unary-part-expanded helper language.
- `FunctionalWithParts2019CorrectedFullCopyRecovery.lean` applies the already verified generic OLD graph embedding decoder to ANY full embedded canonical genuine partial-function structure A in C. It gives a genuinely FULL part-preserving embedding A → wholeMaskOriginalDecode C, identical on vertices, preserving reflection of undefinedness and defined-empty values. Also handles full canonical **tagged** embedded copies. It presupposes the canonical OLD/tagged embedding as input; it does not construct it from an intrinsic nonclosed weak embedding.
- `FunctionalWithParts2019CorrectedGlobalIrreducible.lean` records exactly when global K(H) membership follows from (4b): if **C itself is U-irreducible** and H is isomorphism-closed, the full-carrier induced test is in K(H) and the class membership transfers back along a genuine isomorphism. The hard local candidates may be U-**reducible**.

Each has an explicit active research root and named axiom-check file. New PR remains draft pending actual compilation.

## Critical gaps, not silently discharged

- **Ambient-old vs intrinsic whole-fibre weak tests:** deleting outputs from a nonclosed S can erase the intrinsic domain while an OLD ambient active-domain bit survives. Clipped output restriction differs from whole-fibre deletion for partly surviving multivalued outputs. The two variants agree only in the at-most-singleton output case.
- **Local-premise quantifier direction:** a full original intrinsic weak H-embedding requirement is strictly stronger than an H-valued ambient corrected relative completion requirement on individual tests. The merged total-unary regression has all ambient exact weak tests completed, but no full intrinsic H-completion of one singleton. Conversely, the all-undefined unary example demonstrates another one-test obstruction outside full corrected (4b) coverage. **Neither alone refutes the outer local-class implication.**
- **Vacuity of naive intrinsic-FULL-weak local axiom:** for the nonempty function-closed-hereditary fixed-point-free unary class, a full embedding from any weak singleton into H is impossible, under either clipped or whole-fibre semantics. An all-small-full-weak-completion antecedent at cutoff one therefore forces empty candidates and can satisfy the local implication trivially. This is **not** shown to be a counterexample under the entire irreducible Ramsey-ambient and class-amalgamation package.
- **Global decoded H membership:** source normalization does NOT imply an arbitrary U-reducible C belongs to H. The new irreducibility corollary in PR #902 is designed to make the exact extra hypothesis visible.
- **Nullary function outputs** are excluded from positive-function-arity source-normalization endpoints. Strong functional B-tree sparsening is a separate proof route and is NOT needed for the verified two-pass relational theorem.

## Next genuine mathematical obligation

Decide exactly which weak-substructure and completion semantics the intended original survey appendix theorem claims. For a direct derivation from the original native local-finiteness axiom, prove a **class-level** implication with the correct polarity and all repaired (4b)/control assumptions, or formalize a counterexample satisfying the full package. A per-test full intrinsic embedding ↔ ambient OLD-completion equivalence is false.

The survey manuscript's prose is frozen. Existing and author-commented-out TODO history must be respected; this research note makes no main TeX edits.
