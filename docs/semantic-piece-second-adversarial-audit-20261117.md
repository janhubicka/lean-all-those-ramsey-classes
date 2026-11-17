# Semantic piece equivalence: second adversarial audit (17 November 2026)

**Status:** Finite native-functional amalgamation argument: English proof passes at its stated scope, subject to Lean re-verification. Complete original Theorem 3.17 with all countable witnesses: **not repaired**. Manuscript and Lean code remain untouched.

## Finite proof that survives the audit

Use the new semantic incompatibility relation on **all** compatible rooted contexts. Let finite allowed A and B have the same canonical lift on full closed overlap X. If their native free amalgam D has a forbidden HE-map, choose a connected finite full closed component H of D containing its image. Components C of H\\X on the A-only side have roots R_C=Cl_H(N(C)) in X and full native decomposition H=P_C+_{R_C}E_C. Duplication of P_C along R_C makes it a genuine piece. Equality of lift predicates on X gives equivalent Q_C with an HE-map into B agreeing on the root.

Enumerate **original** A-only components C_1,...,C_t. After replacing earlier C_j by Q_j, the original P_{C_i} remains a full free side with root R_i. Since semantic incompatibility compares **all** rooted contexts (including already forbidden ones), each replacement preserves the existence of an HE-map from some original F into the new connected source. Native HE gluing preserves a map of every resulting source to D. The final source maps entirely into B, contradicting avoidance. No source quotient, injectivization, new function symbols, or Claim 2 minimization is used.

The optional *allowed-context* sharpening can also work: first choose a **minimal closed forbidden** H, so each original E_C is allowed. Later complements may themselves be forbidden: then their extensions are automatically forbidden; otherwise invoke equality of the allowed-context incompatibility sets. This disjunction is essential.

## A genuinely new overrestriction test

Even this allowed-piece/allowed-context sharpening may be too restrictive for infinite signatures. Take L with a symmetric graph relation E and unrelated unary U_i (i in N), and F={C5,C3}, all unary symbols empty in both forbiddens. F is finite and satisfies the printed tuple-surjective HE image closure: noninjective C5 kernels produce a full unlabeled triangle; C3 is irreducible. For each i form a rooted allowed tree P_i with independent root {x,y,z}, private a,b and edges xa,ab,by,za; let U_i(z) hold. Form an allowed rooted star A_i with private c and edges xc,yc,zc, with identical root type. P_i+_{root}A_i contains the HE C5 map x-a-b-y-c-x, which avoids z. Hence the proper incompatibility row of P_i is nonempty. P_i is an actual width-three piece by duplication along the root, but A_i cannot be amalgamated with P_j for j != i because their root diagrams differ. Thus infinitely many active width-three rows arise from one finite printed-image-closed family solely by varying unrelated old symbols.

A parallel native-functional version uses one partial function G_a at each arity a>=2, defining only G_a(z,...,z)=z on the root. The forbidden maps avoid z and the same inflation occurs, despite finitely many function symbols at each arity. This illustrates a serious loss of finite-family applicability, not a refutation of the finite amalgamation implication.

The finite regression checked P_i and A_i are C3/C5-free, the amalgam has ten C5 HE-maps, P_i duplication has exact minimal boundary {x,y,z}, and 12 symbolic labels give 12 different active rows. A separate exhaustive graph-kernel check found 900 noninjective C5 maps to generated images, all producing triangles. These finite checks do not replace an infinite proof or Lean verification.

## Countable and application status

The existing six-cycle/infinite-function-chain construction remains an obstruction to maximal countable witnesses in the literal Definition 3.14; the finite closed-component proof cannot choose a finite closed forbidden H there. Finite or locally finite witnesses are a separate necessary scope specification.

The previous CSS Theorem 4.52 claim that regularity *fails* was not established for **proper allowed** contexts: forbidden pieces are dead predicates, and the unreflexive-order singleton example used contexts forbidden independently of the piece. Mark that particular verdict as **unproved/retracted**, not as a positive regularity proof. The CSS expanded language is infinite, however, so the new root-type inflation demands a genuine finite-interface proof.

Complement-regularity Lemma 3.30 is false under semantic equivalence; replace its use in Theorem 3.18 by the direct finite-orbit argument. Theorem 3.23 and published CSS/ordered applications require separate review.

## Lean marks (no proofs claimed)

- PE-01: exact semantic/allowed piece domain and root-type compatibility — NEEDS_LEAN.
- PE-02: closed component/root decomposition and piece duplication — ENGLISH_CHECKED, NEEDS_LEAN.
- PE-03: sequential original-component replacement with forbidden intermediate contexts — ENGLISH_CHECKED, NEEDS_LEAN.
- PE-04: finite maximal witnesses, strong AP and JEP — NEW_PROOF_NEEDS_LEAN.
- PE-05: arbitrary countable witness lemma — BLOCKED_BY_COUNTEREXAMPLE.
- PE-06: infinite-language piece-type/regularity and CSS Theorem 4.52 — UNVERIFIED.
- PE-07: complement regularity and classification orbit alternative — ORIGINAL_FALSE / REPLACEMENT_NEEDS_LEAN.
- PE-08: Ramsey Theorem 3.23 — SEPARATE_PROOF_REQUIRED.

Keep this PR in DRAFT and do not transfer old Lean validation marks to a changed theorem.