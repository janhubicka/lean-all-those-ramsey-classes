# Track D: completed English argument and final semantic validation

16 November 2026. This supplements `lifts-track-d-actual-theorem-counterexample-round2-20261116.md`, which contains the complete Gamma_m/source/half construction and the binary normalization proof. A consolidated 15-page English note, its editable sources, an explicit labelled m=3 certificate, and four executable checkers were also supplied to the user. No Lean source, kernel certificate, frozen manuscript or theorem-validation mark was changed.

## 1. Exact statement and verdict

Under the literal definitions in the 2019 primary paper, there is a finite relational language with five unary, two binary and one ternary relations and an EHN-antichain F of finite connected structures such that:

* F is regular at every genuine source root width.
* F satisfies the printed TUPLE-surjective EHN image-closure condition, for arbitrary targets including extra vertices.
* Its prescribed distinct-root canonical maximal-lift age fails ordinary AP.
* Its finite forbidden-free shadow class admits NO hereditary precompact relation-only AP lift with exact shadows.
* A fixed closed singleton has infinite Ramsey degree; no countable member is embedding-universal for all countable forbidden-free structures.

The counterexample has no functions, so all old closures are trivial. The infinite conclusions are English deductions, not numerical extrapolations. The proof has no remaining unproved maximal-profile compression premise. It does NOT refute the separate classification theorem assuming an UPWARDS-CLOSED regular forbidden family, nor alternative lifts for each fixed finite forbidden family.

The primary arXiv PDF (1606.07979v4, 3 September 2019) was checked again at Definitions 2.3, 3.13 and 3.14, the tuple-image closure clause preceding Theorem 3.17, Theorem 3.17 itself and Lemma 3.25. The manuscript source anchor remains ramsey.tex blob 652d73b8896ca9884cb9f040d59c4804d63b5823. This is not an inference from a later surrogate Lean definition.

## 2. Core construction and proof obligations, now closed in English

Recall Gamma_m on Z/(3m-1), with edges whose oriented cyclic difference belongs to {m,...,2m-1}; R_m=N(0) is an independent m-set. Triangle-freeness follows from three cyclic gaps of size at least m. Every nonedge has a length-three path, reduced by translation/reversal to 0,m,2m,d. The cyclic interval growth inequality |A+{0,...,t}|>=min(N,|A|+t) proves that separating cuts have size at least m-1.

S_m is two copies of Gamma_m glued on all of R_m. Common roots have unary type C, private sides P and Q; each private half carries the directed chain a_1->b_1->...->a_(m-1)->b_(m-1), with marked Start/End. D-arcs are supported on E-edges and T is empty. Add the finite family Tsmall of every full three-vertex E-triangle with empty T, loopless arbitrary D, and arbitrary unary values. F=Tsmall union {S_m:m>=3}.

For root width n, only m<=n+1 can contribute separating pieces, and Tsmall contributes none. Thus regularity is proved uniformly over the whole infinite family. Unary reflection puts every collided pair of an EHN source map into the same original Gamma_m copy. A source length-three path between the pair yields three distinct image vertices forming an E-triangle. TUPLE-surjectivity forces all target T-tuples absent, making that FULL induced triangle a Tsmall member. Injective tuple-surjective maps already give a full source copy. This proves the exact image-closure condition, without a target-size or vertex-surjectivity assumption.

The Start-to-End P-chain forces m=k for an EHN map S_m->S_k. Seven distinct unary singleton types preclude S_m mapping to a three-vertex member; triangles cannot fully embed into triangle-free sources. Thus the family is irredundant even under EHN maps.

Each decorated target half L_m or R_m^+ collapses all R_m to x, keeps private vertices distinct, and adds T on ALL distinct triples in that half. These maps are full on every source singleton and E-edge, the complete list of nonempty irreducible source tests. An allowed bouquet B(I,J) contains left halves indexed by I and right halves indexed by J, with only x shared. Its exact avoidance criterion is I intersection J empty: T decorations exclude every small forbidden triangle, while a full reflected Start-to-End D-chain forces the same source index in both target sides.

In ANY target containing full matching halves over x, not merely their free amalgam, the two source maps agree on all source roots and combine to an EHN S_m-map. Every source irreducible test stays inside a protected full half. Extra cross tuples and extra vertices cannot change its full table. Opposite private identifications are already excluded by P/Q reflection. This proves permanent incompatibility in arbitrary amalgams.

## 3. New explicit direct contradiction to the published maximal-witness lemma

There are NO source pieces of width one: every S_m has cut size at least m-1>=2 and each small forbidden triangle is irreducible. Hence the canonical lift has no added unary symbols. All added predicates of higher arity are false on a singleton because their tuple coordinates must be distinct.

It follows that both allowed L_m and R_m^+ induce exactly the same canonical expanded singleton X. This singleton profile remains identical in EVERY allowed full extension, so the two sides are genuinely maximal on X under Definition 3.14. Nevertheless their free amalgam admits the EHN map from S_m. Thus they directly contradict the conclusion of Lemma 3.25. This already works for the finite family Tsmall union {S_m} at any fixed m.

The prescribed AGE also fails AP, rather than only the auxiliary lemma. For a fixed finite allowed A, regularity and the distinct-coordinate rule leave only finitely many ground canonical queries on A. Every query is monotone under full extensions. If a current finite witness is not maximal on A, realize a new query in an allowed extension and restrict to the current witness plus the finite image of its witnessing piece. Relational substructures are full on every subset, so this is again finite and allowed. Each step turns at least one of finitely many false queries true; after finitely many steps there is a finite allowed witness maximal on A.

Apply this construction to L_m and R_m^+. Their finite maximal traces induce the same expanded singleton. An AP amalgam in the prescribed age would reduce to an allowed old amalgam of the matching halves, impossible by Section 2. This proves ordinary AP failure without assuming that the original halves were already maximal on their entire carriers. The finite-case failure is of the prescribed canonical construction, not of every alternative finite-family lift.

## 4. Why NO alternative precompact AP lift can retain the infinite shadow

For r indices 3,...,r+2, choose one half at each index according to a binary word eta. The 2^r resulting finite allowed contexts have exactly (r+2)^2-3 vertices. Any two distinct words give opposite matching halves at some index and cannot be amalgamated over their singleton roots.

A general elementary lemma finishes the argument: if t allowed old extensions of X are pairwise nonamalgamable over X, then every hereditary relation-only AP lift with exact shadows needs at least t expansion types over X. Choose one lift of each extension; heredity makes its induced root a lifted member. Equal expanded root types would allow lifted AP, whose old reduct would be the forbidden old amalgam. Applied to t=2^r for all r, this contradicts precompactness of the fibre of the ONE old singleton.

This also explains why local finiteness of closures and cofinal maximalization cannot help. The old root is already closed and remains a full substructure in every relation-only expansion. Opposite rooted half embeddings persist under all allowed extensions. Any cofinal maximizing system must still extend every such context, so the incompatibilities cannot disappear.

The countable diagonal and the infinite-singleton-Ramsey-degree proofs from the preceding note are complete. Universality for finite inputs alone is a different notion: a countable disjoint union can contain all finite contexts, but roots of incompatible contexts lie in different automorphism orbits. Thus no such finite-input universal structure can be omega-categorical.

## 5. Exact positive boundary, without overclaiming

The binary generated-image lemma is proved at unchanged family scope: for any nonempty relational source and any signature of arity at most two, an EHN f:S->D factors through its tuple-generated image Q with BOTH factors EHN. On an irreducible Q-test, singletons reflect unary values, binary loops and optional nullary predicates; each distinct pair has a positive generated binary witness and therefore a source irreducible pair reflecting EVERY binary symbol in both directions. No common irreducible preimage of the whole clique is required.

The second factor is injective EHN, not necessarily globally full. Printed tuple-image closure supplies a full forbidden S' inside Q; its composite into D is an injective original-family EHN witness. Simultaneously for all target subsets U,

    |g^(-1)(U)| = |g(S') intersection U|
       <= |f(S) intersection U| <= |f^(-1)(U)|.

Thus support-minimal injectivization is valid in unary/binary relational languages, without saturation, a finite family or signature, or a uniform source-size bound. This is NOT a completed proof of the remaining binary Claim 2 or the whole binary lift theorem.

The sharp ternary failure is explicit: a C5 with empty T maps to the triangle by (0,1,2,0,1). Adding target T(0,1,2) preserves EHN of the original C5 map, but the tuple-generated triangle inclusion fails EHN on its irreducible full three-vertex source. A stronger VERTEX-surjective full-image-closure premise would repair normalization at arbitrary relational arity; it is a genuinely stronger assumption which this counterexample fails. No functional image-closedness assertion is made.

## 6. Validation actually executed in this continuation

All three previous standalone checkers were rerun unchanged and reproduced their recorded counts and hashes: 40,685 structural kernels/420 EHN quotients/418 noninjective forbidden triangles; 1,520 ordered kernels/155 EHN quotients/153 noninjective ordered triangles; 22,701 binary factorizations with 1,416,753 support inequalities; and all 155 pairwise Boolean obstructions among 30 contexts.

The NEW standalone `audit_track_d_final_semantics.py` imports NONE of those implementations. It computes true induced irreducibility from complete relation tables and all subsets, including ternary-coordinate membership. Its actual run found:

* 270,336 subsets of S3 and S4; 101 actual irreducible source tests including empty tests;
* 3,548 individual permitted cross-tuple insertions into E, D or T, all preserving the forbidden EHN map;
* both fully dense cross extensions and both extensions with an extra vertex carrying every incident positive tuple;
* 31 singleton-deletion connectivity checks and 18 forbidden triangles in generated images;
* 2,064 source tables on one/two vertices with TWO directed binary symbols, a unary and a NULLARY predicate, 4,112 kernels, and all 4,000 compatible image-target extensions;
* all 4,000 generated inclusions EHN, all nullary values reflected, while 1,920 inclusions were not globally full;
* the five-cycle/triangle ternary boundary, accepted for the original source and rejected for the generated-image inclusion.

Every assertion passed. The code also emits a complete labelled m=3 certificate (source tables, fold, half supports, generated and decorated target tables, all irreducible source tests and all generated forbidden triangles). The artifact runner executes four independent scripts and verifies exact expected totals. Finite tests do not quantify over arbitrary infinite targets; the English proof supplies that quantifier.

New checker SHA-256: 72c1e317953345255a2def7694fe281a1b3629716a49649d14368abfd5ec70d3. The primary proof, binary lemma, direct canonical-age consequence and finite validation are complete at this English/computational scope. The infinite native construction is NOT yet Lean-certified, and no external referee review is represented as having occurred.

The ordered/local-completion appendix retains its explicit FINITE-test convention. The direct structural contradiction to Theorem 3.17 and Lemma 3.25 does not depend on that appendix or on an interpretation of infinite tests with finite completions. The separate upwards-closed regular-family classification is not refuted: the semantic upward closure of this F has infinitely many width-one classes, distinguished by the matching decorated halves.
