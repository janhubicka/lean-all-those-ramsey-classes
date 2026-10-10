# Why correcting only Definition 2.17(4b) appears insufficient

**Status:** Mathematical counterexample argument. The key deleted-output
embedding is Lean checked in main; the corrected singleton escape/cardinality
inequality and the "literal completion implies copywise completion" bridge
are being compiled in PRs #32 and #31. An unconditional Lean refutation of
the class-level theorem still needs strong amalgamation in Lean (a complete
mathematical construction is documented in
[paired-strong-amalgamation-proof.md](paired-strong-amalgamation-proof.md)).

## Keep the proposed repair exactly as requested

The *sole* alteration under consideration is:

> (4b) Every **U-closed U-irreducible** substructure of C is in K.

Keep the original Definition 2.15 of U-irreducibility, the ORIGINAL
U-homomorphism-embedding on ALL intrinsically U-irreducible induced
substructures, the original U-completion in (4a), and all original
weak n-vertex tests in (4c).

## The same paired-equivalence class

Let K be finite strict-linearly ordered structures with equivalence E
and a symmetric fixed-point-free total matching M contained in E.
No convexity of E-classes is required. The U-rule has a singleton
E-reflexive root and one M-output (the mate of that root). The
class is U-closed, closed-hereditary and non-Ramsey, as verified in
Lean; its strong amalgamation construction has a complete handwritten
proof and a 72,839-span finite regression but still lacks a general
Lean theorem.

## Any corrected-(4b) candidate C is almost as small as C0

Fix B in K and finite original Ramsey control C0. Suppose a finite
U-closed C satisfies corrected (4b) and literal (4a), i.e. there is
an ORIGINAL 2019 U-completion map f:C -> C0.

If C is empty, the desired size bound is immediate.

Otherwise choose x in C. Its induced singleton C|{x} is intrinsically
U-irreducible. If it were U-closed, corrected (4b) would put this
singleton in K, impossible: K has no singletons. Hence C|{x} is NOT
U-closed.

As C is U-closed, published Lemma 2.23(1) says that {x} cannot
be a relative U-substructure. Therefore there is a tuple of the
matching closure relation with its entire designated root inside
{x}, and a genuine output q outside {x}. By U-closedness the root
is correctly embedded, and the tuple is its UNIQUE output tuple.

The already verified
`IsUIrreducible.of_missing_tuple_in_weak_test` lemma, applied to
the *exact induced deletion* C| (C\{q}), shows this huge weak
substructure is intrinsically U-irreducible. Since f is the
ORIGINAL U-homomorphism-embedding of Definition 2.15, its
restriction to C\{q} must be a FULL induced embedding into C0.
Consequently

    |C| - 1 <= |C0|, hence |C| <= |C0| + 1.

This estimate is independent of B and of the other small local
tests. It is the central obstruction to a (4b)-only repair.

## Local finiteness is once again automatic

Set n(B,C0) = |C0| + 1. Under the corrected antecedent, every C
satisfying (4a) and corrected (4b) has at most n vertices.
The unchanged (4c) therefore tests the WHOLE C (the weak induced
structure on all of its vertices), and directly promises a
(K,U)-completion of it.

A literal U-completion preserves ALL embedded copies of any ordinary
irreducible B, because every such B-copy induces an intrinsically
U-irreducible test. Every B in K is ordinarily irreducible because of
the strict total binary order. Thus that completion is already a
B-copywise completion as required by Definition 2.17(4)'s conclusion.

The case C = empty is covered in the same way: the full empty
test belongs to (4c). The proof uses NO changes to the original
completion map or weak-test semantics.

Therefore K still satisfies the one-clause-corrected local
finiteness condition. Combining this with its mathematically
proved strong amalgamation, with the (Lean-verified) ambient
ordered Ramsey class, and with the persistent non-Ramsey
two-colouring yields a mathematical counterexample to the
**(4b)-only corrected Theorem 2.18**.

## Consequence for future repairs

The proposed single-clause modification is not enough. The
strong near-full-source constraint comes from retaining the
original Definition 2.15 control maps. A promising alternative
is to use genuinely *closed-test* U-homomorphism-embeddings in
(4a) and the local completions and check the appropriate rank
induction, but this would be a SECOND substantive change.
No particular final erratum is accepted until the corrected
general theorem is actually proved. Keep the published prose
frozen, and record only precise TODOs meanwhile.

## Lean proof tasks

1. PR #32: every corrected-(4b) candidate has a genuine escaping
   output and cardinality bound |C| <= |C0| + 1.
2. PR #31: literal K-completion of an exact weak whole-source test
   implies B-copywise completion for ordinary irreducible B, and
   copywise completions pull back across the all-vertices
   induced-substructure embedding.
3. Combine 1 and 2 to prove
   `CorrectedULocalCompletionAt finitePairedClass mateRules B C0
       (Nat.card P + 1)` for ALL B in K.
4. Package corrected class hypotheses and show the corrected
   universal theorem would forbid the verified non-Ramsey K,
   conditional only on K's strong AP.
5. Complete Lean strong amalgamation through the actual
   quotient-class label and root-interval order constructions.

All five steps are compatible with the manuscript freeze.