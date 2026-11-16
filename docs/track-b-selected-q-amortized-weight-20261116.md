# Track B: conditional weighted A+B potential for same-Q source descent

16 November 2026; stacked draft on #1260 (literal selected-Q private
A-source cost telescope), itself stacked on #1250. Frozen 2019 TeX
and collaborator-deleted TODOs untouched.

The key difficulty with the original Claim 2 B→A selected-Q descent
is that TOTAL B-exclusive SOURCE support strictly decreases, but
TOTAL A-exclusive SOURCE support can increase by the exact
positive cardinality of private Q-nonroot SOURCE vertices.
Therefore original global A-minimality is not automatically
preserved at intermediate states, and a naive lex (A,B)
minimum argument cannot be reiterated.

This module defines the natural-number source potential
`Phi_W(s) = A_total(s) + W * B_total(s)`, where all terms
count LITERAL SOURCE vertices rather than image points. It proves:

1. `claim2NativeAFreeQCostedStep_strictWeightedPotential`:
   on a genuine Q+E native forbidden source replacement, with
   the old selected component A-free and exact Q-private
   A-source cost c, **if c < W**, then
   `Phi_W(new) < Phi_W(old)`. This follows from exact
   `A_new = A_old + c` and strict `B_new < B_old`.
2. `claim2NativeAFreeQCostedChain_weightedBudget`:
   for a finite chain retaining each actual selected Q+E
   free-amalgam and exact private cost, if all such costs
   are below W, then
   `steps + Phi_W(terminal) ≤ Phi_W(initial)`.
   The proof makes NO assumption that intermediate source
   states remain original globally A-minimal.

This is a rigorous potential for amortized B→A descent
**conditional on one uniform upper bound on Q-private A cost**.
It is NOT claimed that source finiteness alone yields such
a bound, or that the original common canonical lift
assumptions supply one. A uniform finite forbidden-piece
size bound could be a sufficient geometric input, but the
bound must be derived explicitly from the original family
and the selected-rooted-pattern isomorphism certificate.

Even a globally decreasing potential does NOT eliminate
the real old-root-capture and A-mixed smaller-root exits
at later states: the all-width extremal theorem uses
original A-minimality, not weighted potential minimality.
A strengthened geometric obstruction lemma or a new
global comparison is still needed to complete unrestricted
2019 Claim 2. No weak-map image quotient or new axioms.

Named Lean `#print axioms` and protected proof root added.
Hold DRAFT until exact-head full Lake/Lean, allowed axioms,
no admissions, source contracts and inventory CI, plus parent
PR validation, succeed.
