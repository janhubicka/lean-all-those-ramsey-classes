# Appendix Track B — faithful native H_K and canonical tagged K_H isomorphism closure

6 November 2026. Stacked atop Track B strong-amalgamation transfer PR #905 (itself stacked on #904, #890, #882). No frozen survey prose is touched.

## Semantic problem to avoid

The canonical 2019 K_H class is an image of genuinely partial `Option(Set)` structures. In an arbitrary object, `some ∅` means a **defined empty-valued operation**, distinct from undefined `none`. Native `Structure` uses only set-valued function fibres, encoding undefined as ∅, and does NOT represent independently defined-empty operations. We cannot blindly interpret any arbitrary genuine partial object as native, even if it has the same output-incidence graph.

## Full-embedding reflection into the faithful image

Given a faithful native partite K witness BN and a FULL part-preserving genuine partial embedding `f : A ↪ BN.toNonemptyPartial`, every defined operation `A.func F xs = some U` maps to `BN.toNonemptyPartial.func F (f∘xs) = some (f''U)`. The right-hand side being defined forces the original native target fibre to be nonempty. Equality of complete target fibres then gives `(f''U).Nonempty`, hence `U.Nonempty`. Thus A cannot have `some ∅`.

Consequently its faithful native roundtrip `A.collapseDomain.toNonemptyPartial = A` holds on the **literal original carrier**. The full partial map collapses to a full native map `A.collapseDomain ↪ BN.toStructure`. Native K heredity places the source in K. Pulling back relation transversality, full function-output fibre transversality, and vertex parts through the injective map gives an actual partite `System` on the original source carrier. This system witnesses genuine H_K membership of A.

No surjectivity is used: H_K is closed under full part-preserving subembeddings in the faithful essential-image sense. The published 2019 class only requires the weaker isomorphism-closure implication.

## Lean endpoints

- `nativeKFaithfulH_isomorphismClosed_of_free`: `GenuinePartiteIsomorphismClosed2019 H_K` from native `Structure.FreeAmalgamationClass K`. Full embeddings preserve independent definedness; source-defined original-partial homomorphisms do NOT suffice.
- `nativeKCanonicalTagged2019_isomorphismClosed_of_free`: the tagged canonical 2019 relational K_H image is `IsomorphismClosed2019`, by the already green original tagged K_H pullback theorem.

This discharges the isomorphism condition of the corrected coordinated 2019 multiamalgamation theorem for the faithful native class image. Remaining independently required conditions include inclusion into a chosen irreducible ambient Ramsey class R and the ambient-relative exact-weak local-completion axiom (Track C). The strict full-functional mixed-root B-trees remain separate Track D.

This is an unverified proof attempt until exact-head CI, full Lean build, import/source integrity audit and named `#print axioms` all pass. No artificial axiom or `sorry` is used, and there are no manuscript edits.
