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


### Exact n-vertex side-HULL budget; necessary overrun certificate

The additional two declarations make the quantitative gap in the
published n-VERTEX axiom completely explicit. Suppose a weak Whole
has a genuine full relatively U-closed free diagram over an
**ORDINARY IRREDUCIBLE** Root embedded in a U-closed corrected-(4b)
candidate C. If the *ambient U-closure hulls* of the two weak side
images each contain **at most n actual vertices**, the n-vertex
weak-test premise H-completes those exact closed hulls. The
already verified #1052 ambient-support gluing then completes the
ORIGINAL weak Whole. No closed generator-rank-j premise is used.

Contrapositively, if such Whole is NOT H-completable, then
**at least one** of these two auxiliary closed side hulls has
strictly more than n vertices. The weak sides themselves need
not be large. The result pinpoints *one specific cost* of using
the original vertex cutoff instead of generator rank, without
assuming a hull isomorphic to the tested source.

These lemmas still do not select any free diagram, establish
that the actual Picture history keeps the hull sizes below n,
or solve U-reducible root hulls. The overrun certificate is a
necessary condition for failure, not proof that it occurs
in the intended construction. Both lemmas have dedicated
`#print axioms` checks and remain DRAFT until full CI.

### Closed free cuts: the literal vertex cutoff excludes rank-one roots

Two further conditional endpoints use the verified
`IsFreeAmalgam.root_isUClosed_of_closed_whole_and_sides`
(local partite #578) and the verified original H-valued rank-one
gluing theorem (ATR #1050). For a genuinely U-closed free Whole
with U-closed sides of at most n VERTICES, the original actual
ambient weak n-vertex test completions supply H-completions of
the two sides. The root is U-closed automatically; if its
USize ≤1, corrected (4b), H-isomorphism closure and H-strong
amalgamation glue them to complete the exact Whole.

Contrapositively, every eligible CLOSED proper free cut of a
noncompletable weak Whole under these same explicit hypotheses
has common-root USize at least 2. This is a sharper rank-two
barrier WITHOUT assuming completability of arbitrary closed
hulls of generator rank ≤n, and without assuming a missing
intrinsic-to-ambient class-locality bridge.

These remain PROOF CANDIDATES until full exact-head CI and
named axiom checks pass; the two original merged input theorems
are green.

### Stronger closed-root statement: U-reducible, not just rank at least two

A final refinement removes the rank-one numeric assumption from
the *positive* closed-root gluing lemma. By merged local #578,
a U-closed free Whole of U-closed sides has an intrinsically
U-closed common Root on the **same** carrier. If this Root
is also U-irreducible (at ANY generating rank), corrected
(4b) and H-isomorphism closure place it in canonical K(H).
The original n-vertex hSmall premise completes both sides,
and verified #938 protected-root gluing completes Whole.

Consequently every eligible such closed cut of a bad
source has **U-reducible** common Root. This is strictly
stronger than merely proving its USize is at least two,
and remains a conditional theorem until exact-head Lean
CI passes. It still does not produce an eligible free
cut or solve U-reducible root gluing.
