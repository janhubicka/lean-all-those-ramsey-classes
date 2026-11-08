# Appendix Track B — adversarial finite obstruction to the irreducible ambient host

8 November 2026. Stand-alone Lean regression, independent of the Track B Ramsey assembly PR #911 and native-output PR #914. The survey manuscript remains frozen. Nothing here alters the corrected two-pass proof or local-completion hypothesis; this is an audit of its attempted application.

## The dangerous simultaneous hypotheses

The conditional end-to-end theorem assumes a relational class R satisfying both:

- the canonical tagged image K_H of the faithful native functional class H_K is a subclass of R;
- every member of R is **ordinary irreducible**, meaning every pair of distinct vertices belongs to a common relation tuple.

Hence every K_H-member would have to be irreducible. This is a necessary consequence, not a theorem that holds for all native K.

## Concrete two-vertex counterexample

Take the original native functional language with **no relation symbols and no function symbols**, one part PUnit and two isolated vertices `Fin 2`. Let K be the class of ALL native structures. Its hereditary and free-amalgamation class axioms are tautological.

The native two-vertex partite system is transversal. Its faithful genuine Option(Set) presentation with the same vertex parts lies in H_K. Its 2019 complete-mask/full-root-tagged relational representation lies in the canonical K_H image. Since there are no original function symbols, *no* positive-output domain mask, output mask or closure tag can exist. The only remaining nonempty symbols are **unary predicates naming the unique part**.

Therefore no relational tuple can contain both distinct vertices; the canonical tagged structure is not irreducible. Consequently no R (Ramsey or otherwise) can both contain all of K_H and consist entirely of ordinary irreducible structures.

## Lean declarations and scope

The proposed regression checks:

1. `allNativeClass_freeAmalgamation`: the native K really is a free-amalgamation class.
2. `twoIsolatedTagged_mem`: exact tagged two-vertex member of canonical K_H.
3. `allTaggedSymbolsUnary`: every symbol remaining in the tagged syntax is unary, including complete-mask syntax and closure tags, proven by eliminating the absent original function symbols.
4. `twoIsolatedTagged_not_irreducible`: the two distinct vertices cannot be linked by any single tuple.
5. `no_universally_irreducible_host`: the two ambient assumptions from the assembled theorem are jointly contradictory in this basic example.

If Lean verifies this example, the conditional PR #911 / #914 theorem remains a logically valid implication but **must not be advertised as a general native free-amalgamation Ramsey result**: one must first construct an appropriate irreducibilizing (usually ordered) expansion, adapt the canonical K_H class to it, and prove descent back to the original function language. This challenge is separate from the global ambient-relative weak-test local-completion issue (Track C).

No `sorry`, `admit` or new axiom is used. Named axiom checks and active source-root inventory added. Draft until full exact-head CI verifies the regression; do not add a green manuscript marker or restore removed TODOs.
