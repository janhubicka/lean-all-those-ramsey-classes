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

## Scope and limits

- Source-side native K-membership, genuine H_K membership and canonical tagged K_H membership have now been given explicit interfaces, not conflated. There is no assumption that all arbitrary defined-empty Option(Set) structures arise from native systems.
- On nonclosed weak S, the commuting identity is FALSE in general and K_H membership of induced ambient tagged tests is not asserted.
- This does NOT prove that native K has the stated heredity condition, nor imply canonical K_H strong amalgamation, isomorphism closure, or the 2019 ambient-relative local K-completion predicate. The latter is the independent Track C obstruction, and strict functional mixed-root B-trees remain Track D.
- Clipped multivalued weak restrictions and whole-fibre complete-value 2019 restrictions remain distinct.
- Code includes no admits/sorries or added axioms. Named `#print axioms`, active-root registration, full exact-head Lean build, import and axiom audits required before integration. No survey TeX changes.
