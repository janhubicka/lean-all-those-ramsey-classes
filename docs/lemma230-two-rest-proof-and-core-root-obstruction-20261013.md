# Lemma 2.30: the genuine two-REST proof and the precise remaining root problem

**Detailed English proof — 13 October 2026. Internal author note.**
This supplements docs/lemma230-detailed-english-native-proof-20261013.md. It is not an edit to the frozen published 2019 manuscript.

The earlier two-*copy*-range method supplies a vertex-exact A-letter boundary when their Hales–Jewett parameter sets are disjoint, but the *two copy ranges themselves* do not always form a free relational cover. An alternative two-*REST* construction fixes that relation-crossing problem unconditionally and turns the remaining obstruction into an exact closed-boundary question.

## 1. Actual native attachment, positive maps, and two REST sets

Let X=Attach(D,S,R^N,(m_k)_{k∈I}) be the genuine simultaneous native attachment, with its core R^N and full attached copies of old D indexed by I. A vertex is either a core vertex or a PRIVATE exterior vertex labelled by its unique attachment index k. No global injectivity or intrinsic closedness of a temporary attachment is assumed.

For distinct indices i≠j define

    REST_i := {z∈X : z is not private exterior of attached copy i},
    REST_j := {z∈X : z is not private exterior of attached copy j}.

**Proposition 1 (genuine two-REST free cover).**
The two induced target structures X|REST_i and X|REST_j form a relational free cover of the WHOLE X, over their literal intersection, for every relational language and any number of further attached copies. No assumption about Hales–Jewett parameter-coordinate transversality or closure of the attaching support is needed.

**Proof.** Every core vertex belongs to both REST sets. Every private exterior vertex is labelled by exactly one k and hence belongs to at least one of REST_i and REST_j because i≠j. Thus the two vertex sets cover X and meet on their literal intersection.

Every native relation tuple has one of two construction sources. If it is a *power-core* relation tuple, every entry is core and hence the entire tuple belongs to BOTH rest sets. If it arises from the attached copy k, then:
- for k=i it lies entirely in REST_j, because no vertex of an i-copy tuple is private exterior of j;
- for k=j it lies entirely in REST_i;
- for k different from i,j it lies entirely in BOTH rest sets.

Since each REST is an induced substructure, every positive relation tuple arises wholly from at least one side and both directions of the relational free-amalgam relation equivalence follow. Its overlap embeddings are literal induced inclusions. This proves the claimed **actual** relational free cover. ∎

**Corollary 2 (arbitrary original source).** If p:F→X is ANY positive relational homomorphism, even one identifying unrelated source vertices and even for a nonclosed exact weak source F, define

    L := p⁻¹(REST_j),   M := p⁻¹(REST_i),   H := L∩M.

Positivity and Proposition 1 imply an exact free relational diagram
    F = (F|L) *_(F|H) (F|M).
This is the proved positive free-cover pullback theorem (#137), applied to the two-rest target cover. If some source vertex maps to private exterior of i and another to private exterior of j, those witnesses give both sides proper. If |F|≤r+1 then |L|,|M|≤r. These are *source vertex* bounds, not closure-generator bounds. This is the intended result of Lean PR #176.

## 2. Old-Picture maps of the TWO RESTS, with only i,j source-active

Let now X be the genuine Hales–Jewett attachment of the selected old partite Picture. Assume p:F→X is an ORDINARY homomorphism-embedding, possibly noninjective, and the set of original source-private-active indices is contained in {i,j}. No constraint on the number of POWER CORE vertices is made. These hypotheses hold, for example, when an intrinsic rank-at-most-two source has a bad active history and the positive generator estimate has identified exactly a transverse pair.

**Proposition 3 (two ordinary old REST maps).**
Each of the exact induced source sides F|L and F|M from Corollary 2 has an ordinary homomorphism-embedding into the previous old Picture D. Different genuine parameter coordinates can be used for the two maps.

**Proof.** Consider L=REST_j preimage. By definition NO vertex of F|L projects to the private exterior of j. Because the only active indices of all F are i,j, every private-active attached copy index seen by F|L is i. (The actual core remains untouched.) Choose a coordinate k_i in the nonempty parameter set of the genuine Hales–Jewett line ℓ_i. Restrict p to exact L and use the verified source-active-subhistory factorization: every projected L vertex belongs to the induced native subattachment retaining the entire power core and just the attached old copy i. Coordinate evaluation at k_i on the core, together with the identity on that sole attached old copy exterior, is an **ordinary** homomorphism-embedding of this subattachment into D by the verified selected-coordinate fold lemma. Composing gives the desired p_L:F|L→D.

Likewise the source M=REST_i preimage has at most the private-active index j. Choose its (possibly distinct) genuine parameter coordinate k_j and repeat the argument to obtain p_M:F|M→D. The proof uses no common global Hales–Jewett coordinate and no closure of the exact tested source. ∎

This is the precise new interface of Lean PR #177. It combines naturally with PR #176, but neither individual statement establishes the completion of the whole source.

## 3. The exact common REST root is CORE, not necessarily one A-word

Under the same *only i,j source-active* hypothesis, the common root H=L∩M consists exactly of source vertices whose images are in the POWER CORE. Indeed a source vertex in H is not private exterior of i or j, and no other private-active index is used. It must therefore be core. This is a simple case distinction on actual native vertex tags and is the second intended theorem of PR #177.

**Important obstacle.** The two old maps p_L and p_M on H are coordinate evaluations at k_i and k_j of those core vertices. They have the same outer part map, but there is no reason for the original core vertices to lie in a single word embedding of A. Consequently, there need not exist full induced old embeddings a_L,a_M:A→D and one q:H→A satisfying BOTH vertex-exact equations

    p_L(s_L(r))=a_L(q(r)),
    p_M(s_M(r))=a_M(q(r)).

A tiny witness: take A a one-vertex structure with a loop, D={0,1} with the reflexive order ≤, and the two-coordinate core D². Both core vertices z=(0,0) and w=(1,1) belong to the intersection of the two REST sets. A core-root source containing these vertices and relation z≤w evaluates at either coordinate to the DISTINCT old vertices 0 and 1. No full embedding of the singleton A can have both 0 and 1 in its image. The root can be supplemented by two private exterior source vertices to ensure both active indices without changing this obstruction on the core. This defeats a **fixed-A-boundary assertion for arbitrary two-REST roots**. It is NOT an obstruction to gluing via a larger closed K-root, nor a counterexample to the theorem.

## 4. What the general proof actually needs

The new free REST cut solves the relational-cover and strict-source-cardinality steps **without assuming source tuple localization**. The two old REST maps solve the ordinary-side-map step whenever only i,j are source-active. For a maximal intrinsic-rank exact weak source on at most r+1 vertices, each REST side is small and its ordinary map is protected by the maximal-size lemma.

The only still-missing geometric ingredient in this genuine two-active case is a **compatible CLOSED K-boundary Q** containing the entire core-root image under both side maps, with full vertex-level embeddings into the old Picture, together with rank-r completion budgets for the projected side hulls. It cannot simply be labelled the original A. A possible proof strategy is to use the closed K-hull of the root's image when that image admits a *compatible* K-completion, and then apply a RELATIVE rooted completion invariant rather than unrooted W_r. This must be proved; it is not a consequence of pairwise part equality.

For three or more source-active indices, the two-rest free-cover result remains true for any pair i≠j, but either REST may contain further active lines without any common parameter coordinate. The ordinary old map construction of Proposition 3 is therefore no longer available unless a new recursive history lemma is proved.

For the **original stronger closed rank-(r+1)** Lemma 2.30 there is a separate numerical obstruction: a proper free cut of a closed source with generating rank r+1 does not bound either side's absolute vertex count by r; the source may have very many closure-output vertices. The projected closed-root and side rank costs must be accounted for explicitly.

**Status:** Propositions 1–3 are the correct conditional native strategy. The all-rank and multi-line compatible-boundary successor is OPEN. Neither the prior two-copy completion nor the new free REST split proves the full corrected Theorem 2.18.
