# Track C: ambient U-irreducible root-hull gluing

12 November 2026. Additive proof work, stacked on #1053 (which depends
on #1052); the frozen survey text has not been changed.

This branch weakens the ordinary-irreducible Root hypothesis of the
#1052/#1053 gluing statements. For an actual free weak cut in one
corrected-(4b) ambient C, it is enough that the **ambient U-closure
hull of the original weak Root image** is U-irreducible. This hull is
closed because C is closed, and (4b) supplies it as a canonical K(H)
object. The verified ambient-support glue then completes the SAME
original weak Whole from H-completions of the two side hulls.

If the two weak sides have at most j vertices, the hRank closed
generator-rank-j premise already supplies side-hull completions. The
contrapositive says that for a noncompletable weak Whole, **every**
small proper relatively U-closed free cut has a root with
U-reducible ambient closure hull. Ordinary-reducible weak roots
with U-irreducible hulls are therefore not obstructions.

This is a conditional theorem, not the printed higher-rank induction.
The remaining case is U-reducible *ambient closed hulls*, together
with the independent gap between the constructor's generator-rank
premise and the survey's fixed vertex-cardinality local hypothesis.
No use of fixed-B coverage, arbitrary root canonicality or source
carrier enlargement.

New module, named axiom audit and registered active root. Keep draft
until exact-head CI build, no-admission scan and protected-root audit
pass, and until parents are merged.


## Why this is a genuinely weaker boundary condition

For a concrete closure-graph example, take a four-vertex directed
cycle (0 \to 1 \to 2 \to 3 \to 0) in a language with the
binary graph relation of a (single-valued) unary function. Let U
require closure under that unary function and let the original
weak Root be the induced subset \`{0,2}\`.

The Root is **ordinarily reducible**: there is no graph relation
between its two vertices, and it is the free amalgam of its two
singletons. Nevertheless, its ambient U-closure hull is the
whole four-cycle. The only U-closed induced vertex sets of a
directed cycle are the empty set and the entire cycle. Thus
the hull is U-irreducible, although its original weak Root was
ordinary reducible. If we also add one nondistinguished four-ary
relation tuple on all four vertices, the closed hull becomes
**ordinarily irreducible**, without introducing any relation tuple
on the two-vertex weak Root. Thus this separation persists even
when the potential K(H) boundary must be ordinary irreducible.
This is an explanatory finite example, not a claimed separate
Lean finite-model regression or a model of all class-level axioms.

It explains why the new theorem is more than a restatement of
the old irreducible-Root hypothesis: the actual obstruction is
the inability to find **one canonical closed boundary**, not raw
Gaifman reducibility in the original weak intersection.
