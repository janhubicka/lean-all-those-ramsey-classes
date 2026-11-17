# Revised piece equivalence: proof and application audit

17 November 2026. **English proof and executed finite regressions only; no new Lean certification.** Baseline main: `37e3dfb92f222364b6302feb1df3b139dd0b0ccd`. Manuscript: `ramsey.tex`, blob `652d73b8896ca9884cb9f040d59c4804d63b5823`.

The latest local patch replaces incompatibility by existence of an original forbidden homomorphism-embedding into the connected free amalgam, and considers all finite pieces having a nonempty incompatibility set. Regularity remains finite index at each width. **The literal patch does not pass the full audit.** The finite/locally finite functional argument below passes the present English audit, but there are two scope problems and one false inherited lemma. The numbered manuscript and all Lean source are untouched.

## 1. Replacement proof for finite witnesses

Let K=Forb_he(F), with finite connected forbidden sources. Let A,B be finite allowed structures with common full closed substructure X and equal amended canonical lifts on X. Suppose H is a connected component of A+_X B admitting a forbidden map. If H lies on one side, contradiction is immediate. Otherwise, for each component C of the Gaifman graph of H minus X lying in A minus X, set

R_C = Cl_H(N_H(C)), P_C = H[C union R_C], E_C = H[H minus C].

R_C is closed and contained in X. Both P_C and E_C are full closed substructures and H=P_C+_{R_C}E_C. For positive-arity partial functions this follows directly: a function on arguments in C union R_C either has all arguments in the closed root, or touches C, in which case any output outside C is a neighbour and belongs to R_C. A function from the complement into C would contradict closedness of X or join two components outside X.

P_C rooted on R_C is an actual piece: freely duplicate P_C over R_C. The two private copies of C have neighbourhood closure exactly R_C, so R_C is a minimal separating cut. This avoids assuming that R_C was a minimal separating cut in H itself. P_C is allowed because it embeds in A, and its rooted complement in forbidden H witnesses nonempty semantic incompatibility.

The inclusion P_C -> A realizes its canonical relation on the distinct root coordinates. Equality on X gives Q_C equivalent to P_C and an HE map Q_C -> B with those same root values. The full ordered root structures agree: a common element of the nonempty incompatibility sets has a defined free amalgam with both pieces.

Replace the original A-only components successively by fresh Q_C's. Each whole structure remains connected because the connected replacement attaches at the same nonempty root. Semantic equivalence preserves the existence of an HE map from some original member of F; it does NOT assert that the replaced structure itself belongs to F. At the end, identity on the retained B-part and the chosen maps of the Q_C's glue to an HE map into B. Every irreducible CLOSED source test is contained in one full side of a source free amalgam: otherwise its intersections with the two sides form a proper free decomposition. Composition gives a forbidden map into B, contradiction.

No source injectivization, image quotient, support minimization, intermediate minimizer assumption, or old Claim 2 iteration occurs. Original functions are retained.

The proof extends to locally finite countable witnesses: the finite forbidden image and finite overlap have finite closed supports in the two sides. Under regularity, finite extension-maximization terminates, since a fixed finite carrier has finitely many additional relation instances. A finite-maximal witness is maximal against locally finite extensions, because a finite piece image together with the old witness has finite closure there. This proves the finite-witness hereditary strong amalgamation conclusion, with free old-language shadows, under the explicit scope convention.

## 2. The unrestricted countable witness lemma fails

Use unary C,P,Q, symmetric binary E, a partial unary s and partial ternary G. Let S be the coloured six-cycle

r0-p0-p1-r1-q0-q1-r0,

with C={r0,r1}, P={p0,p1}, Q={q0,q1}, and both functions nowhere defined. Let T consist of all finite irreducible structures in this language containing an E-triangle; put F={S} union T.

This family satisfies the printed tuple-image closure: T members are irreducible, hence map fully. For S only r0=r1 can be identified in an HE map (the same-colour P and Q pairs are edges). If identified, triangles appear, and tuple-surjectivity forces the functions to remain everywhere undefined, yielding a full finite irreducible triangle. An injective tuple-surjective map yields a full S copy.

The amended regularity holds. T maps are side-local in any free amalgam. Remaining crossing maps come from the fixed finite source S, hence are described by finitely many source-side assignments and root maps at fixed root size. The old language is finite, so there are finitely many root diagrams.

Make a C,P,P triangle with root x and define G on every permutation of its distinct vertices to a0; attach s(ai)=a(i+1) along an infinite uncoloured ray. Call this core T_P, and use a C,Q,Q core T_Q similarly. X={x} is closed. No finite closed substructure contains a core triangle, so neither core admits a forbidden T member; S is excluded by the missing opposite colour.

Let V be the free union over X of all finite allowed rooted extensions of X, one copy of each isomorphism type. Set W_P=T_P+_X V and W_Q=T_Q+_X V' with disjoint copies. These are allowed. Every finite allowed branch is triangle-free, since the finite closure of a triangle is irreducible and belongs to T. An S map whose P and Q pairs lie in different branches forces both C roots to x and a triangle on both branches; only the core can contain one. If both pairs lie in one branch, the whole map lies in that forbidden-free branch.

Both W_P and W_Q realize every possible unary canonical piece predicate on x. Any finite piece mapping into an allowed extension is itself allowed, its closed singleton root is fully mapped to X, and that rooted piece is present in V. Higher-arity predicates vanish on a singleton by the distinct-coordinate rule. Thus both witnesses are maximal on the same lifted X, even against arbitrary countable extensions. Their amalgam admits S by identifying r0,r1 with x and mapping the P and Q pairs into the two cores. Source irreducible tests are only singletons and edges, where the new functions remain invisible.

This is a counterexample to the literal unrestricted Lemma 3.25, NOT a proof that every finite-age homogenization fails. A viable scope correction is to require witnesses and their extensions to have finite closure of each finite subset. This excludes no finite structures or function arities. It must be explicit.

## 3. A published application fails the raw regularity patch

In Theorem 4.52 (HN19, Section 4.4.2), the CSS application introduces F_{a,i} for every positive a, with distinct input coordinates, and forbids ordered irreducible structures not in Age(U^+).

For each a>=2 the ordered singleton X_a with F_{a,1}(x,...,x)=x and all other functions undefined is such a forbidden structure. Add one private vertex and connect it to x by the order relation. Duplicating this two-vertex structure over x makes an actual width-one piece P_a. P_a is incompatible with the singleton X_a; different a have different full root structures and different nonempty incompatibility sets. Thus the enlarged universe has infinitely many width-one classes. This is an actual failure of the revised regularity assumption in a published application, not a disproof of its Ramsey conclusion.

Exclude pieces P already outside K: they never HE-map to allowed witnesses and their predicates are always false. This removes those unused classes. BUT it is not a complete infinite-language repair. With an EMPTY order on X_a and a single nonreflexive order arc in P_a, the analogous pieces are allowed (all forbidden sources are nonempty weakly ordered and have reflexive order). An arbitrary rooted context may privately contain an ordered forbidden member and connect it to x; the piece is active again. These pieces are not weakly ordered. Hence the appropriate ambient/root-diagram convention must be explicitly audited; it is not legitimate to assume all pieces are weakly ordered when the definition says all finite connected structures.

The CSS finite effective F2 and admissible-root-type argument, its printed closure bound, and the Ramsey transfer remain obligations. Existing manuscript TODO ATRC-066 is not a completed Lean certificate.

## 4. Complement regularity is false; use a direct orbit proof

For directed cycles of prime lengths p>=3, a path of length m rooted at its endpoints and a return path of length k have forbidden free amalgam exactly when m+k is prime. Infinitely many rows occur: equality of two rows would make primality eventually periodic with period d, forcing the composite p(1+d) to be prime for a sufficiently large prime p. But the complementary family contains both singleton types and forbids every nonempty structure, so its semantic regularity is trivial. Therefore Lemma 3.30 must not be retained under the new equivalence.

For the reverse implication of Theorem 3.18, instead record the sets of Aut(U)-orbits of root tuples attained by FULL embeddings of allowed pieces into the omega-categorical universal U. Two rooted structures have an allowed free amalgam iff these orbit sets intersect. Equal-root embeddings into U give an allowed amalgam; the natural map from the free amalgam into it is HE by irreducible side containment. Finitely many tuple orbits give finitely many incompatibility rows. No complement-family lemma is needed.

## 5. Lean re-verification marks

These are audit obligations, NOT new Lean declarations or green validation marks:

* PE-01: semantic incompatibility/equivalence and exact domain of pieces — DEFINITION_CHANGED_NEEDS_LEAN.
* PE-02: forbidden/irrelevant roots and CSS regularity — APPLICATION_REGULARITY_FAILURE.
* PE-03: component boundaries, both closed sides, duplication into a minimal-cut piece — NEW_ENGLISH_PROOF_NEEDS_LEAN.
* PE-04: root coherence and preservation of original forbidden maps under semantic replacement — NEW_ENGLISH_PROOF_NEEDS_LEAN.
* PE-05: finite Lemma 3.25 — NEW_ENGLISH_PROOF_NEEDS_LEAN.
* PE-06: unrestricted countable Lemma 3.25 — BLOCKED_SCOPE, with counterexample above.
* PE-07: Definition 3.14 witness convention and finite maximal witness extraction — NEW_ENGLISH_PROOF_NEEDS_LEAN.
* PE-08: old flip/Claims 1--2 proofs — retain their old contracts, do not transfer their marks to the new proof.
* PE-09: Theorem 3.17 hereditary/JEP/strong AP/precompactness/generic assembly — REASSEMBLY_NEEDS_LEAN.
* PE-10: Lemma 3.30 — FALSE_UNDER_REVISED_DEFINITION; replace its use, not its proof alone.
* PE-11: Theorem 3.18 direct full-embedding orbit argument — NEW_ENGLISH_PROOF_NEEDS_LEAN.
* PE-12: Theorem 3.23 finite control, completion and lift-property argument — SEPARATE_RAMSEY_AUDIT_REQUIRED.
* PE-13: finite-forbidden Corollary 3.24 — finite-interface regularity proof needed; ordered reduction remains separate.
* PE-14: Example 3.16's exact predicate counts and Corollary 4.9 unary arity conclusion — REVERIFY_PRESENTATION_AND_ARITY.
* PE-15: Theorem 4.52 / ATRC-066 — APPLICATION_REGULARITY_FAILURE; ambient admissibility unresolved.
* PE-16: `TrackDProtectedHalvesObstruction.lean` / `noAllowedRootedAmalgam_of_protectedForbiddenHalves` and `compatibleFunctionalFold_isEHNHomomorphismEmbedding` — definition-independent building blocks; unchanged, no fresh build claimed.

## 6. Published-use and execution boundaries

Finite-signature finite forbidden families, fixed odd-girth/Petersen graphical instances, and bipartite parity profiles retain finite continuation tables. Precise canonical arity counts need separate review. Later uses in *Echeloned Spaces* invoke HN19 Corollary 4.2, and *Higher arity stability and the functional order property* uses the hereditary locally finite subclass theorem (its Theorem 6.14): those are not applications of the revised regularity condition. This is not an exhaustive census of citations or a validation of all their other proofs.

Primary sources: HN19 DOI 10.1016/j.aim.2019.106791, arXiv 1606.07979v4; https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/echeloned-spaces/2A35174EF5425D30946E008CB31FB4AE ; https://link.springer.com/article/10.1007/s00029-025-01055-4 .

Executed finite regressions reuse the explicitly identified previous functional-table library: 7202 models, 28124 closed overlaps, 22376 component decompositions, 73665 irreducible side tests, 13260 duplicated-piece/fold checks. The six-cycle checker exhausted 203 kernels (exactly two valid), tested 1107 rooted triangle-free finite branches against each core, and checked finite tail closure growth. Finite truncated cores are forbidden and are NOT claimed to instantiate allowed infinite witnesses. These checks are not universal proofs or Lean certification. The complete English note, scripts and results are supplied as conversation artifacts.
