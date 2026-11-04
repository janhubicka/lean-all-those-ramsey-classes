# Appendix Track B — actual native EHN Stage versus canonical 2019 H/K image

**November 3, 2026.** A cross-repository source/class correspondence, continuing merged partite-construction PRs #535, #543 and #548. The frozen survey text is not modified.

## Exact source object

Let T be an ACTUAL finite `FunctionalPartite.EHN.Stage K D`. Its native set-valued function structure has empty outputs on undefined inputs, and part map `T.system.part`. The faithful `Structure.toNonemptyPartial` produces a genuine `Option(Set)` source on **exactly** `T.Carrier`, with `none` for empty native fibres. It does not pretend arbitrary defined-empty `some ∅` is represented by native `Structure`.

Encode this genuine object using `withPartsWholeMaskOld` and `wholeMaskTagExpansion`, including unary part predicates, every OLD complete-value/domain mask, and all fresh full equality-pattern U-closure roots. Call the result `genuineEHNStageCanonical2019Tag T`. It is not a separately reconstructed relational Picture.

## New Lean theorem contracts

- `genuineEHNStageCanonical2019Tag_mem_iff`: for ANY original genuine class H and the ACTUAL native finite stage T, the canonical tagged Stage belongs to the canonical relational class K_H exactly when the faithful native partial object belongs to H. Native EHN `K` membership alone does not imply H membership: the latter is an **explicit hypothesis**.
- `genuineEHNStage_closed_iff_canonical2019TagInduce_UClosed`: for positive primitive function arities and ANY literal S⊆T.Carrier, **native full functional closedness of S** is equivalent to U-closedness of the AMBIENT tagged structure induced on exactly S. Output part transversality is inherited from T; no vertex hull or weak-domain recomputation.
- `genuineEHNStage_inducedCanonicalK_mem_iff_closed`: if H is closed-hereditary and contains the actual native faithful partial T, **K_H membership of the induced canonical tagged Test on S** iff S is native function-closed. Forward direction uses that every K_H member is U-closed; reverse uses genuine H hereditary under actual full functional closed restriction and the canonical K closed-heredity theorem.

The third theorem is the missing easy positive/negative class dictionary. It proves that a nonclosed intrinsic weak test is **not automatically a canonical K_H member**. The corrected 2019 proof must instead use an induced *semi-closed AMBIENT test* and the separate relative local completion axiom. This prevents the false replacement of an ambient tagged weak test with the canonical tagged intrinsic whole-fibre weak function.

## Proof scope and dependencies

This proof uses existing green 2019 class membership, canonical tagged U-closedness, and induced-closed heredity, with the older source interface `EHNStage`, `toNonemptyPartial`, native/partial closure, transversality, and `withParts` root masks. It intentionally avoids changing the upstream Lake dependency pin or importing the newer Track B source modules, so it remains compatible with other ongoing upstream validation tracks.

Not proved: arbitrary intrinsic local-finiteness ⇒ the ambient-relative 2019 K-local axiom (Track C), full strict B-tree completions (Track D), or a homomorphic equivalence of native Hales–Jewett powers with naïve coordinatewise OLD/tag powers (refuted in Track B's finite regression).

**Validation:** the module and all named endpoints require exact-head CI, import audit, and `#print axioms` before green promotion. No manuscript changes or author-removed TODO restoration.
