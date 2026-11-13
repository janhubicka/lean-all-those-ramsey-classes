# Track C: B-active source counts under a genuine selected-Q replacement

13 November 2026. Stacked on #1134 (itself stacked on #1132). CI / permitted-axiom checks pending.

New source: `AllThoseRamseyClasses/Lifts/Claim2ActualOuterBActiveCard.lean`.

## Exact counting interface

For a genuine OLD/NEW full native complement E and selected Q, with
*exact* NEW outer carrier `Q ∪ E(OldPart)`, no Q vertex mapping into
the chosen B-active target region, and identical old/new target values
on E, prove that:

1. `fullNativeSelectedOuter_Bactive_card_eq_retained`:
   the number of B-active SOURCE vertices in NewPart equals the number
   of B-active retained E SOURCE vertices originally lying in OldPart.
   This needs no finite-carrier assumption.

2. `fullNativeSelectedOuter_Bactive_card_le_old`:
   on a finite old source, the new B-active SOURCE count cannot exceed
   the old outer B-active SOURCE count.

3. `fullNativeSelectedOuter_Bactive_card_lt_old_of_missing_retained`:
   with finite old/complement sources, if at least ONE old outer
   B-active SOURCE vertex is not in the old complement image, the
   inequality is strict. The exact missing-source hypothesis appears
   explicitly rather than being smuggled in from target-image ranks.

The proof uses a private genuine source embedding
`retainedBIntoOld` and exact carrier identity from #1134, never
injectivity of the WEAK target map. The strict inequality uses
`Fintype.card_lt_of_injective_not_surjective`.

This discharges a clean finite-counting step relevant to the 2019
Claim 2 induction. It does **not** assert the actual geometric
carrier and no-new-B-Q conditions of #1120 have been connected to
this generic counting theorem, nor exclude smaller-root old-root
capture or A-mixedness, nor establish the zero-rank terminal exit.
The actual geometric same-witness composition remains open.

Original numbered manuscript unchanged; no collaborator TODOs
reinstated. Three named `#print axioms` certificates and protected
active root. All statements remain draft until exact-head Lean CI.
