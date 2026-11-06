# Track B: exact closed restriction commutation and native K → H_K heredity

4 November 2026. Stacked atop Appendix Track B draft PR #882, independently from the genuine whole-weak rank/relative-completion draft PR #875. The survey manuscript remains frozen.

## Precise commuting square

For native `Structure A` and an actual function-closed subset S, the TWO complete genuinely partial structures on literal carrier `S` are equal:

```
toNonemptyPartial (A.induce S hS)
    = (A.toNonemptyPartial).induceClosed S
        ((A.toNonemptyPartial_isClosed_iff S).mpr hS)
```

Unlike arbitrary weak restriction, no originally nonempty native function output disappears when its inputs are in S, because hS places all such outputs in S. Thus both sides preserve the complete output set and definedness. Empty native fibres remain `none`; no `some ∅` domain is invented. The proof explicitly checks nonempty ambient fibres iff the induced subtype fibre is nonempty. There is no closure hull substitution, added vertex, new part label, or arbitrary weak full embedding.

## Original H_K transfer

The new `NativeKClosedHereditary2019 K` class axiom says: for every finite, transversal native partite `System B` whose native underlying structure lies in K, every genuinely native-function-closed induced `B.induce S hS` is ALSO in K. This is a meaningful additional hypothesis on K, NOT a theorem for arbitrary K.

Under this hypothesis, `nativeKFaithfulH_closedHereditary` proves that the faithful genuinely partial H_K image from draft PR #882 is closed hereditary in the exact 2019 sense. The proof chooses the original source B witnessing H_K, forms the native closed restriction on literal S, uses the class axiom to retain membership in K, then uses the literal commutation identity above to identify it with the genuine Option(Set) closed restriction of A. The inherited part map is exactly B.part ∘ Subtype.val.

Consequently `genuineEHNStage_nativeKHereditary_inducedK_iff_closed` can use the verified PR #851 exact K_H closed induced test iff, now under an explicit NATIVE K closed heredity assumption rather than an unexplained H_K hereditary hypothesis.

## Reverse direction: an exact equivalence of hereditary properties

The additional theorem `nativeKFaithfulH_closedHereditary_iff` establishes both directions:

```
NativeKClosedHereditary2019 K
  ↔ GenuinePartiteClosedHereditary2019
       (nativeKFaithfulGenuinePartiteH2019 K)
```

For the converse, let B be a genuine native K partite system and S a genuinely function-closed subset. H_K closed heredity yields an H_K witness C for the exact Option(Set) `induceClosed` of `B.toNonemptyPartial` on S. The first theorem identifies this exactly with `(B.induce S).toNonemptyPartial`. Taking `collapseDomain` on both sides returns **literally equal native structures**, because the faithful native conversion satisfies `toNonemptyPartial_collapseDomain`. Thus K membership transports to the actual native `B.induce S`, with no isomorphism-invariance assumption and no modification of parts or carriers.

This is the sharp class-property transfer, conditional only on the stated property itself; it does not prove native K possesses that property. Named axiom check added, pending CI.

## No extra native heredity axiom for the free-amalgamation application

The actual functional `Structure.FreeAmalgamationClass K` interface
already has `hereditary`: whenever `K B` and there is a FULL native
functional embedding `A ↪ B`, then `K A`. For a genuinely
function-closed S, `Structure.inclusion B.toStructure S hS` is
precisely such a full embedding. Thus the Track B
`NativeKClosedHereditary2019 K` condition is not an independent
assumption for the native EHN theorem.

Three named Lean endpoints formalize this reduction:

- `nativeKClosedHereditary_of_freeAmalgamationClass` uses
  `hFree.hereditary` and the LITERAL native closed inclusion;
- `nativeKFaithfulH_closedHereditary_of_freeAmalgamationClass`
  transfers it to the faithful original genuine H_K class;
- `genuineEHNStage_freeAmalgamation_inducedK_iff_closed`
  characterizes canonical tagged K_H membership among induced
  ambient tests of an ACTUAL EHN Stage under precisely the native
  FreeAmalgamationClass hypothesis already used by the construction.

This does not derive the unrelated 2019 H_K strong-amalgamation
or relative-local-completion hypotheses, which require independent
checks. No claim is made for a nonclosed weak test.

## Scope and limits

- Source-side native K-membership, genuine H_K membership and canonical tagged K_H membership have now been given explicit interfaces, not conflated. There is no assumption that all arbitrary defined-empty Option(Set) structures arise from native systems.
- On nonclosed weak S, the commuting identity is FALSE in general and K_H membership of induced ambient tagged tests is not asserted.
- This does NOT prove that native K has the stated heredity condition, nor imply canonical K_H strong amalgamation, isomorphism closure, or the 2019 ambient-relative local K-completion predicate. The latter is the independent Track C obstruction, and strict functional mixed-root B-trees remain Track D.
- Clipped multivalued weak restrictions and whole-fibre complete-value 2019 restrictions remain distinct.
- Code includes no admits/sorries or added axioms. Named `#print axioms`, active-root registration, full exact-head Lean build, import and axiom audits required before integration. No survey TeX changes.
