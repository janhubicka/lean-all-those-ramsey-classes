# Track B: source-stage weak rank and relative local completion, 4 November 2026

Companion to merged [PR #851](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/851) in the 2019 formalization and merged partite-construction PRs #535, #543, #548. Frozen survey manuscript unchanged.

## Checked source and exact carriers

An actual finite native functional EHN `Stage K D` is interpreted as a genuinely partial `Option(Set)` structure via `T.system.toStructure.toNonemptyPartial`. The vertex part map is `T.system.part`, retained by naming unary parts *before* applying the 2019 complete OLD domain/output masks and full-root closure tagging. The result is the already verified `genuineEHNStageCanonical2019Tag T` on the original carrier `T.Carrier`.

For every arbitrary literal subset `S : Set T.Carrier` and seed `Q : Set S`, no assumed closedness of S is needed. In particular `S` and `Q` are never replaced by the ambient-generated full functional closure.

## New exact contracts

1. `genuineEHNStage_wholeWeakFunctionClosure_eq_taggedUClosure`: the genuine whole-fibre `Option(Set)` weak functional closure inside S equals the 2019 `UClosureHull` in the *ambient-induced* complete-mask tagged relational object restricted to exactly S.
2. `genuineEHNStage_wholeWeakGeneratedByAtMost_iff_taggedUSize`: the intrinsic minimum number of weak functional generators on S is bounded by n **iff** the 2019 USize of that precise tagged induced weak source is bounded by the same n.
3. `genuineEHNStage_exactWeak_KCompletion_iff_HRelative`: a corrected relational induced-closed U/K_H completion of this exact weak source is equivalent to the independently defined genuine H-valued ambient-*relative* completion of the same source. **Neither direction proves that any completion exists.**

The proofs compose earlier verified native nonempty-defined partial translation, output transversality, `PartialSetStructure.withParts_wholeWeak_*` and `wholeWeak*inducedAmbientU*` dictionaries, plus `canonicalGenuineTagged2019_KCompletion_iff_relative`.

## Essential distinctions

- A multivalued function with some—but not all—outputs in S has a **clipped** weak value different from its **whole-fibre** weak value. The new equalities apply only to the genuine whole-fibre Option(Set) restriction and the corresponding complete-value 2019 closure description. They are not an equivalence with the clipped output-part-split tagged USize.
- The ambient induced OLD domain records persist even when the complete functional application is deleted from the intrinsic whole-weak structure. No replacement of the ambient tagged test by a freshly tagged intrinsic weak structure is allowed.
- Exact `USize` means the least cardinality of a generating set in the tested weak structure, **not** the cardinality of the ambient closure hull, which could be larger.
- Stage's native `K` membership does **not** automatically mean its faithful partial form belongs to a chosen original H. No such H membership is required for the closure/rank dictionaries or the formal equivalence of local completion predicates; actual K_H membership remains explicitly handled by PR #851.
- The 2019 original-functional intrinsic-local axiom ⇒ ambient-relative U/K_H local axiom remains **open in Track C**; strict B-tree completion remains **open in Track D**.

Named `#print axioms` declarations, active source root, full Lean build and import audit are mandatory before merging. This draft does not add a green marker or alter any author TODO.
