# Appendix Track B — full strong amalgamation of H_K and canonical tagged K_H

6 November 2026. Stacked after native free/partite strong amalgamation PR #904, which itself follows the faithful H_K class image PR #882 and its closed-heredity transfer PR #890. Survey text stays frozen.

## The missing class property

The corrected 2019 theorem needs the canonical relational K_H class to have finite strong amalgamation. This cannot be inferred by mere citation to the native K class because the canonical image requires named parts and full Option(Set) embeddings, including the independent definedness bit.

The faithful image class H_K consists only of genuine partial structures **equal on their literal carrier** to `B.toStructure.toNonemptyPartial` for an actual native output-transversal partite System B with K B.toStructure and identical vertex part labels. No defined-empty `some ∅` input lies in the image.

1. `PartialSetStructure.Embedding.toCollapsedNative` turns a genuine FULL Option(Set) embedding into a full native embedding of the two `collapseDomain` structures. This uses all function-fibre equality and domain reflection, not merely source-defined partial homomorphisms. Its vertex map is exactly the original one, and it works even with some-empty in the *general* source, since collapsing to native deliberately forgets the independent domain bit.
2. `nativeKFaithfulH_strongAmalgamation`: for a full part-preserving span in genuine H_K, choose its existing native K-system witnesses with exactly equal carriers and part maps. Collapse the full embeddings back to full native partite maps (the faithful nonempty-defined roundtrip recovers the original native structures), apply the preceding true native K-partite strong amalgamation, and re-encode the actual native transversal target faithfully as an H_K member. Both partial embeddings are full and part preserving; agreement and exact overlap are literal the same functions from the native diagram.
3. `nativeKFaithfulH_strongAmalgamation_of_free` uses the verified original native `Structure.FreeAmalgamationClass K` and the genuine native attached-amalgam theorem of PR #904 to discharge the entire original-2019 H_K strong amalgamation class axiom.
4. `nativeKCanonicalTagged2019_strongAmalgamation_of_free` combines this with the already green canonical tagging strong-amalgamation theorem, establishing finite strong amalgamation of the full OLD complete-mask, full-root-tagged relational class K_H. The map agrees on all original part labels and true function values, including isolated vertices and repeated input arguments.

## Delimitations

This source-class transfer proves the strong-amalgamation class property of the faithful H_K image, **not** that an arbitrary unrelated 2019 H contains the native EHN objects. It does not assert that all genuine Option(Set) structures have native witnesses or treat `some ∅` as an undefined input.

It also does NOT prove the class-inclusion hypothesis into a specified irreducible ambient Ramsey class R, isomorphism invariance of the faithful image class under arbitrary carrier bijections, or the critical original-intrinsic ⇒ ambient-relative local completion axiom (Track C). The strict mixed-root B-tree targets remain separate.

## Validation

Native H/K source and all four new strong endpoints have named `#print axioms` checks. Exact-head full Lean CI must pass on each stacked PR before any integration or green manuscript marker. No source file outside the new dedicated Track B module and its checks/docs/inventory is edited.
