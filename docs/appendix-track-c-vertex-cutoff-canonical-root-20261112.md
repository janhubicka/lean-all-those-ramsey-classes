# Track C — rank-free canonical-root free-cut theorem at the ACTUAL n-vertex cutoff

12 November 2026. New Lean proof candidate, not yet CI-validated.

The previously merged Track C conditional rank steps use a closed
U-generating-rank-j completion invariant. The printed corrected 2019
local clause (4c), by contrast, provides only completions of all
exact ambient OLD weak induced tests with ≤n **vertices**.

This new theorem keeps the latter, weaker and original predicate.
If the candidate C satisfies the exact n-vertex weak-completion
premise, then EVERY full embedded weak side of at most n vertices
has a genuine H-relative completion. We compute its exact image
in C (at most n vertices), take that test's H-completion and
precompose with the full embedding. No hulls or source enlargement.

Consequently, if a given noncompletable weak source S has any
proper free decomposition into relatively U-closed sides with at
most n vertices, its common Root cannot belong to canonical K(H):
otherwise the established H-valued strong-amalgamation theorem
#938 would glue the two H-completed sides. This yields a true
VERTEX-cutoff obstruction lemma, without assuming corrected (4b),
H-isomorphism closure, C U-closedness, an ambient rank bound, or
existence of a canonical cut.

### Limits

1. The n-vertex input `hSmall` is already a premise of the
   ambient-relative class-local axiom, **not** something the
   original intrinsic functional local axiom has been shown to
   supply. This bridge must not be treated as the missing
   intrinsic-to-ambient implication.
2. The theorem cannot manufacture a free cut, guarantee relative
   U-closedness of the sides, or make a U-reducible common Root
   into an H-member. It therefore does not give an unconditional
   rank increment or a class counterexample.
3. All maps preserve the same exact source carrier and old masks.
   A canonical H target is allowed to depend on each small test.

Four proposed named axioms checks, one active-root marker, no
existing proof edits and no manuscript changes. Keep draft until
exact-head full Lean compile, axiom and admission checks pass.

### Sharper root obstruction under corrected (4b)

The additional declaration `genuineTagged2019_badWeak_vertexCutoff_root_closure_or_irred_failure` assumes the original H-isomorphism closure and corrected (4b), and derives from the same exact n-vertex weak-test premise that every eligible small relatively closed free cut of a noncompletable S has a Root which is **either not intrinsically U-closed or not U-irreducible**. The proof uses the verified original H↔K isomorphism transport and canonical K-coverage of embedded closed U-irreducible tests. It never upgrades hSmall to the stronger closed generator-rank hypothesis and does not construct a common boundary for U-reducible roots.
