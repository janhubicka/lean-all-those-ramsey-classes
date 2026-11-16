# Track D: actual lift-theorem counterexample, second English audit, and binary repair

16 November 2026. English proofs and finite independent checks only. No new Lean declaration, no kernel-certification claim, no frozen-manuscript changes. The target is the literal unrestricted theorem in `ramsey.tex`, blob `652d73b8896ca9884cb9f040d59c4804d63b5823`, not a substitute finite-family theorem. This note records the actual antichain counterexample, not the older redundant marked-core family in #1255/#1263.

## 1. Finite closures do not bound permanent singleton choices

Precompactness follows if an adequate lift has finitely many new symbols of each arity and forbids repeated-coordinate tuples: on a fixed a-vertex closed structure only arities up to a can contribute. The difficult issue is adequacy for amalgamation. The construction here has NO functions, so every singleton is closed, but forces arbitrarily many permanently incompatible extensions over the same singleton.

### Base graph

For m>=3 let Gamma_m have vertex set Z/(3m-1) and symmetric loopless adjacency xEy iff y-x modulo 3m-1 lies in {m,...,2m-1}. It is triangle-free: the three cyclic gaps of a triangle would each be at least m, exceeding circumference 3m-1. Every nonedge has a length-three path: after translation and reversing endpoints it is 0,d with 1<=d<m, and 0,m,2m,d works.

Every separating set has size at least m-1. For any nonempty cyclic subset A, |A+{0,...,t}|>=min(N,|A|+t), since adding a shift by 1 enlarges every nonempty proper subset. If deleting Z separates a surviving component C, then W=C+{m,...,2m-1} is contained in C union Z and misses another component. The interval bound gives |C|+m-1<=|W|<=|C|+|Z|, hence |Z|>=m-1.

Let R_m={m,...,2m-1}=N(0), an independent m-set. Name a_j=j and b_j=2m+j-1 for 1<=j<m. Outside R_m, vertex 0 is isolated and a_jEb_k iff k<=j. Every private vertex has a neighbour in R_m.

### Forbidden family

The relational signature consists of binary E,D, ternary T, and unary C,P,Q,Start,End. No function symbols occur. Form S_m by gluing two copies of Gamma_m along all of R_m, with no other cross tuples. Mark the common root C, the two private sides P and Q. In each side put exactly the D-chain a_1->b_1->a_2->b_2->...->a_(m-1)->b_(m-1), with the indicated Start and End. Put T empty. Then |S_m|=5m-2 and the Gaifman graph is triangle-free, because all D-arcs are already E-edges.

Let Tsmall be all isomorphism types of three-vertex structures with E the loopless complete graph, T empty, D any loopless directed relation, and arbitrary interpretations of the five unary predicates. This is a FINITE set of irreducible sources. Put F=Tsmall union {S_m:m>=3}, with isomorphic copies understood, and K=Forb_EHN(F).

### Exact original hypotheses

All sources are finite, nonempty and connected. Deleting fewer than m-1 vertices from S_m leaves both graph copies connected and at least one common root vertex surviving. Thus a selected root of width n can occur only in S_m with m<=n+1. Only finitely many finite sources contribute at each fixed positive width; each has finitely many ordered rooted pieces up to full isomorphism. Tsmall has no separating-cut pieces. This is the printed regularity condition, indeed a stronger finite-isomorphism-type property.

For the PRINTED tuple-surjective image-closure clause, take any tuple-surjective EHN f:S_m->H. If f is injective, tuple-surjectivity makes its FULL induced image exactly S_m. Otherwise singleton reflection forces a collided pair to have the same C/P/Q type, hence to lie in one original Gamma_m copy. It is nonadjacent because an edge is irreducible and maps injectively. A length-three path between that pair maps to an E-triangle on three distinct vertices. Tuple-surjectivity and empty source T force T^H empty. Singleton reflection makes both binary loops false on the triangle. Thus the FULL induced triangle belongs to Tsmall. This works even when H has extra vertices. A source in Tsmall is itself irreducible, so any EHN target map already supplies a full forbidden copy.

The family is IRREDUNDANT, even under EHN maps. S_m->S_k must map its P-labelled directed Start-to-End chain to the unique target chain, forcing 2m-3=2k-3 and hence m=k. S_m has seven distinct unary singleton types and cannot EHN-map into a three-vertex source. A forbidden triangle cannot embed fully in triangle-free S_m. Between three-vertex irreducibles, EHN maps are full isomorphisms.

## 2. Decorated halves and permanent incompatibility

Collapse all of R_m in one source half to a single C-root x, keeping private vertices distinct. Retain all old unary values and D-arcs, and make T true on ALL ordered triples of pairwise distinct vertices of the resulting half. Call the P version L_m and the Q version R_m^+. Each has 2m vertices. Its E-graph has x adjacent to every private vertex and a_jEb_k iff k<=j; D is the same directed chain. The common full singleton has only C true and all loops false.

The collapse is genuinely EHN: source irreducible tests are exactly singletons and E-edges. Unary types, both directed D-values, E, loops and all repeated-coordinate ternary tuples reflect on each such test. New T-tuples require three distinct vertices and are therefore not seen by those tests.

Let B(I,J) be the free union over x of L_i for i in I and R_j^+ for j in J, where I,J may be finite or countable. Then

    B(I,J) in K  iff  I intersection J is empty.

No Tsmall source embeds fully: each E-triangle lies in one half, where T on its distinct coordinates is positive. Any EHN S_k->B(I,J) must map its P-labelled D-chain, including both marked endpoints, to a single target P-chain. Those chains have no cycles, branching, or arcs through x, so this forces k in I. The Q-chain forces k in J. Conversely, when k belongs to both, combine the two explicit source-half collapses.

The matching-half obstruction holds in EVERY amalgam. Given any full copies of L_m and R_m^+ in a target D agreeing at x, compose the two source-half maps with those full embeddings. Their roots all map to x, so the maps agree there. Every positive source tuple and every actual irreducible source test is inside one protected full half. Their union is therefore EHN S_m->D, regardless of arbitrary extra cross-relations. Private opposite-side identifications are additionally forbidden by reflected P/Q types. Thus no allowed D can contain both matching rooted halves.

## 3. Boolean strengthening of the finite obstruction

For r>=1 and every word eta in {0,1}^{3,...,r+2}, let A_eta contain L_m if eta(m)=0 and R_m^+ otherwise, freely sharing x. Each is allowed, and every one has

    |A_eta| = 1 + sum_(m=3)^(r+2)(2m-1) = (r+2)^2-3.

Two distinct words differ at an index m, supplying opposite matching halves. Hence these 2^r finite extensions of the SAME old singleton are pairwise nonamalgamable over it.

Any hereditary relation-only AP lift with exact shadows K must assign pairwise different induced singleton expansion types to all A_eta. Otherwise amalgamation over their common expanded singleton would yield a forbidden old amalgam. The fibre over this ONE singleton therefore has size at least 2^r for every r: no precompact such lift exists.

This lower bound also holds for the finite truncation F_r=Tsmall union {S_m:3<=m<=r+2}. It does not contradict existence of some precompact lift for each fixed finite family; the required finite number of singleton types can grow with r. It does invalidate passing to the infinite family while retaining a fixed finite root code.

Equivalently, the graph of finite rooted extensions over X, with edges for pairs having no allowed amalgam over X, must be finitely colourable in any precompact AP lift. Here it contains cliques of order 2^r for every r. This is a target-extension obstruction, not a source-closure-size calculation.

## 4. Direct countable diagonal and Ramsey consequences

For any countably infinite allowed U enumerate its vertices u_0,u_1,... . At m=i+3 choose R_m^+ if a rooted L_m embeds over u_i, and choose L_m otherwise. The bouquet containing exactly those choices is allowed, but cannot embed in U: if its root maps to u_i, the chosen half at i+3 is either absent there or incompatible with the half already present. Finite universal candidates are ruled out by arbitrary finite size. Thus there is no countable embedding-universal allowed structure for all countable members.

For the finite Ramsey obstruction, take the disjoint union B of the 2^r Boolean contexts. It is allowed because every source is E-connected and therefore maps into one component of any E-disjoint union. In any allowed target D, colour a copy of X by the Boolean context embedding over it, if any, with a fixed default otherwise. At most one context can occur over a vertex. Every B-copy contains all 2^r root colours. Hence the singleton Ramsey degree is unbounded. The ordered version works with orders extending the block orders.

All these left/right choices persist under allowed extensions; maximalization cannot identify opposite choices. This is NOT the older counterexample where a single blue triangle made every displayed live observation true.

## 5. Positive boundary: binary generated-image factorization

Let L be any relational language of arities at most two, let S be nonempty, and let f:S->D be EHN. Define the tuple-generated structure Q on Y=f(S) by R^Q=f[R^S] for every symbol. The factor q:S->Q is vertex- and tuple-surjective EHN. On each irreducible source test, generated positive tuples lie in D, so full reflection by f also gives full reflection by q. This part is true at every arity.

**Binary image lemma:** the inclusion j:Q->D is also EHN (though not necessarily globally full).

Proof: take an irreducible induced I in Q. Its Gaifman graph is complete. At each vertex y choose a preimage s. Fullness of f on the source singleton reflects every unary value and diagonal binary tuple; optional nullary symbols reflect there as well. For distinct y,z in I, some positive binary Q-tuple witnesses their adjacency. Tuple generation supplies distinct preimages s,t sharing a positive source binary tuple, so S[{s,t}] is irreducible. Fullness of f on this pair reflects EVERY binary symbol on (y,z) and (z,y), not only the symbol witnessing adjacency. Reflected tuples are then in Q by generation. There are no higher-arity tuples to check, so j restricted to I is a full embedding. Therefore j is EHN.

No global irreducible preimage of I is assumed; separate pairs may use different source witnesses. This is exactly why binary arity is enough. An EHN inclusion need not be globally full: two independent vertices can include EHN into a directed edge.

**Original-family normalization corollary:** if F is any family of finite nonempty sources in this unary/binary language satisfying the PRINTED tuple-image closure, every forbidden EHN f:S->D has an injective original-family EHN replacement g:S'->D with

    |g^{-1}(U)| <= |f^{-1}(U)|

for every target subset U. Apply closure to q:S->Q to obtain a full forbidden e:S'->Q. Then g=j composed with e is injective EHN, and its image is contained in f(S). Therefore

    |g^{-1}(U)| = |g(S') intersection U|
       <= |f(S) intersection U| <= |f^{-1}(U)|.

At a global source-support minimum this gives equality and an INJECTIVE support-minimal witness from the ORIGINAL family. No saturation, finite family, source-size bound, root-cover premise or finite signature is needed. This repairs the normalization step in binary relational languages, NOT the remaining Claim 2/whole lift theorem or arbitrary native functions.

## 6. Exact ternary failure and stronger-closure repair

In the actual counterexample, the tuple-generated image of S_m under the fold has the same unary/binary tables as L_m ⊕_X R_m^+, but T is empty. It contains m(m-1) irreducible E-triangles. In the actual target all these triangles have positive distinct-coordinate T. Thus the generated-image inclusion is NOT EHN: the full forbidden triangles supplied by printed closure cannot be transported to the target.

Already a five-cycle with empty T, mapped to a triangle by (0,1,2,0,1), exhibits this: adding a distinct-coordinate ternary tuple preserves EHN of the original five-cycle map but destroys EHN of the generated-triangle inclusion. Arity three suffices for the normalization failure, whereas the lemma above rules it out at arity at most two.

At arbitrary RELATIONAL arity, a genuinely stronger family premise would repair normalization: require that every VERTEX-surjective EHN image contain a full forbidden member. Apply this to the actual FULL induced image D[f(S)], whose source factor is EHN; the resulting full forbidden embedding has no greater source support. This premise is not printed tuple-image closure. The current counterexample fails it: its decorated image is vertex-surjective EHN-forbidden, contains no full forbidden triangle, and cannot contain S_k because it has only one C-vertex while S_k has at least three.

No full positive theorem under this strengthened premise is asserted here, and no functional range-closedness assertion is smuggled in. For native functions a finite EHN image need not be closed; adjoining its finite closure does not preserve the support bound for free.

## 7. Ordered/local-finiteness audit boundary

The earlier detailed note also constructs weakly ordered forbidden sources by adding a unary upper-level predicate and orienting E-pairs by the three proper colour levels. Full ordered target halves respect those levels, and tuple-generated quotient triangles have the same transitive order. The source vertices a_1,...,a_(m-1) have distinct images under any EHN map into a finite control C0: for i<j, D(a_i,b_i) and not D(a_j,b_i) are both reflected on source E-edges. Thus m-1<=|C0| and the forbidden-witness bound is 5|C0|+3. The detailed artifact separately proves the actual finite completion statement by extending the partial order without changing irreducible tests or creating a forbidden map. This is explicitly a FINITE-test local-completion claim, not a convention requiring an arbitrary infinite test to have a finite completion. The main structural counterexample does not depend on this additional ordered assertion.

The complete ordered proof and original checker remain in the supplied `track_d_actual_counterexample_20261116` bundle. This repository note gives the structural proof and the new binary lemma in full; it does not mark the ordered construction or any new result Lean-certified.

## 8. Executed audit evidence

The previous checker was rerun unchanged: 40,685 structural kernels for S3/S4, 420 EHN quotients, 418 noninjective forbidden-triangle witnesses; separately 1,520 ordered kernels, 155 EHN quotients, 153 noninjective ordered-triangle witnesses. All PASS. Baseline SHA-256: dcb0a265d8bc4c2025acf870fbbb41ad89f8a7eda8736c961c0141ab1b26a055.

The NEW independent binary checker exhausts all 4,165 unary/directed-binary source structures on <=3 vertices (loops allowed), all 20,613 canonical kernels, and 22,701 compatible target tables on their images. Every generated factor and inclusion is EHN; 18,048 inclusions are NOT globally full. It checks 120,473 induced irreducible image tests and 1,416,753 support inequalities. PASS.

A second NEW independent construction checks m=3,...,8, 717 full source tests and 2,666 protected image tuples. All 53,960 cross binary/ternary tuples lie outside every tested image, confirming finite invariance under arbitrary cross additions. It verifies 30 equal-size Boolean contexts for r=1,...,4, all 155 pairwise Boolean obstructions, and 166 generated-image irreducible triangles which fail ternary reflection. PASS.

These are finite sanity checks after the English proofs, not an infinite proof by experiment and not Lean certification. The new generic checker and provenance record accompany this note. Frozen numbered manuscript unchanged; no new Lean files or validation marks. The separate upward-closed regular-family classification theorem is not refuted: the semantic upward closure and full-range saturation of this family themselves have infinitely many genuine one-root incompatibility classes (matching decorated halves give the identity matrix).