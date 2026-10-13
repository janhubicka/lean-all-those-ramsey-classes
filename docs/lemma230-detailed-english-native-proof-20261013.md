# Lemma 2.30 (2019): detailed English native proof and remaining obstruction

**Internal proof note — 13 October 2026.** The published 2019 mathematical prose remains frozen. This document distinguishes a COMPLETE conditional proof, verified in Lean, from the genuinely unresolved general Hales–Jewett successor step. All structures and maps are the actual native ones, not an invented abstract attachment.

## 1. Exact hypotheses and induction contracts

Let \(L\) be a finite relational language with closure description \(\mathcal U\), and let \(\mathcal K\) be a strong-amalgamation class of finite irreducible \(\mathcal U\)-closed structures, hereditary for closed substructures. Fix \(A,B\in\mathcal K\). In the genuine Hales–Jewett Picture step, the old closed Picture \(D\) is replaced by \(P\), built from a partite coordinate power together with attached copies of \(D\) indexed by actual Hales–Jewett lines. The corrected protected projection of \(P\) lands in that *temporary attachment*, not generally in old \(D\).

The printed Lemma 2.30 seeks a closed-Picture successor completing every closed test of intrinsic \(\mathcal U\)-generating rank at most \(j+1\). The alternative exact weak-vertex-size condition completes every literal induced weak test on at most \(j+1\) vertices. These are distinct invariants:

\[
 R_j(D):\quad \forall H\text{ closed in }D,\quad
 \operatorname{USize}(H)\le j\Longrightarrow H\text{ has a corrected K-completion};
\]
\[
 W_j(D):\quad \forall T\subseteq D,\quad
 |T|\le j\Longrightarrow D|T\text{ has a corrected K-completion}.
\]

A completion of a small *weak generating set* does not automatically extend to its prescribed much larger closed hull. Upstream PR #234 supplies a finite adversarial example. The strengthened uniform rooted invariant \(W_j^{\mathcal K}\) allows an entire embedded closed irreducible K-root in addition to \(j\) weak vertices. Lean proves its zero base and preservation along already available protected maps, but not that the actual native step promotes \(W_j^{\mathcal K}\) to \(W_{j+1}^{\mathcal K}\).

## 2. COMPLETE PROOF: exact two-copy transverse source localization

**Proposition.** Let \(F\) be a finite exact weak relational structure, with an ordinary homomorphism-embedding \(p:F\to X\) into the **actual** native attachment
\[
X=\operatorname{Attach}(D,S,R^N,(m_i)_{i\in I}).
\]
Choose distinct copy indices \(i\ne j\) whose genuine Hales–Jewett lines have disjoint parameter-coordinate sets. Assume:

(i) every original source vertex \(u\in F\) projects into the full embedded range of attached old copy \(i\) or attached old copy \(j\);

(ii) **every relation tuple of the original source** projects wholly into copy \(i\) or wholly into copy \(j\) (the choice can depend on the tuple);

(iii) some original source vertex projects into copy \(i\)'s private exterior, and another into copy \(j\)'s private exterior;

(iv) \(\operatorname{USize}(F)=|F|\le j_0+1\), where \(j_0\) is the previous rank bound; and

(v) old \(D\) has the **closed rank-\(j_0\)** completion invariant, while the stated strong K-amalgamation, closed heredity, irreducibility and closed \(A\in\mathcal K\) conditions hold.

Then the ORIGINAL exact weak \(F\) has a corrected \((\mathcal K,\mathcal U)\)-completion.

### Step 1 — the literal induced free source cover

Define the source vertex sets by inverse image of the actual attached copy embeddings:
\[
L=\{u\in F:p(u)\in D_i\},\qquad
M=\{u\in F:p(u)\in D_j\},\qquad
H=L\cap M.
\]
Hypothesis (i) gives \(L\cup M=F\). Because these are *literal* subsets of the original source carrier, their induced inclusions are full relational embeddings and their intersection is precisely \(H\). Hypothesis (ii) says that every source relation tuple lies entirely in \(L\) or entirely in \(M\). Thus, directly from the definition of relational free amalgam,
\[
                         F=(F|L)*_{F|H}(F|M).
\]
No source vertices have been added or replaced by a hull. This argument does not use that the whole native coordinate power is freely decomposed into its two line images; that stronger claim is **false** (see Section 3).

### Step 2 — properness and the true size estimate

A private exterior vertex of native copy \(i\) cannot belong to any distinct copy \(j\): such a vertex is tagged by its unique copy index. Hence hypothesis (iii) supplies a source vertex in \(L\setminus M\) and another in \(M\setminus L\). Both induced source sides are proper. Since \(|F|\le j_0+1\),
\[
                            |L|,|M|\le j_0.
\]
This is a bound on original SOURCE SIDE VERTICES. It is NOT a statement that the potentially larger ambient closed hulls of their projected old images contain at most \(j_0\) vertices.

### Step 3 — the old-copy side maps

The ordinary homomorphism-embedding \(p|_L:F|L\to X\) has image in the full induced image of copy \(i\). By the checked factor-through-embedded-copy lemma, it factors as an ordinary homomorphism-embedding \(f_L:F|L\to D\), satisfying
\[
                 p(u)=\operatorname{copyMap}_i(f_L(u))\quad(u\in L).
\]
Likewise \(p|_M\) factors through the true embedded copy \(j\) to an ordinary \(f_M:F|M\to D\). No global injectivity of \(p\) is assumed; the reflection on irreducible tests passes through the full copy embeddings.

### Step 4 — ONE actual vertex-exact A-letter root

On the common source \(H\), the copy factorization equations give
\[
 \operatorname{copyMap}_i(f_L(r))
 =p(r)=\operatorname{copyMap}_j(f_M(r))\qquad(r\in H).
\]
Because \(i\ne j\), the two original old vertices \(f_L(r),f_M(r)\) cannot lie in their private exteriors. They belong to the ACTUAL attaching support, and their line maps into the common coordinate power are equal. Since the two Hales–Jewett lines have disjoint parameter-coordinate sets, the verified transverse line-overlap theorem produces TWO *full induced* letter embeddings \(a_L,a_M:A\hookrightarrow D\) and ONE map \(q:H\to A\) with
\[
                   f_L(r)=a_L(q(r)),\qquad
                   f_M(r)=a_M(q(r))\quad(r\in H).
\]
These are equalities of old vertices, not merely equality of their part labels. The map \(q\) may identify distinct root vertices. Its image's \(\mathcal U\)-closure INSIDE the prescribed closed \(A\) is a genuine closed K-member by closed heredity, and both actual letter embeddings restrict to embeddings of that *same* closed boundary into \(D\). No independent arbitrary completion targets have been glued by fiat.

### Step 5 — the corrected K-completion

Maximal intrinsic \(\mathcal U\)-size of \(F\) implies maximal intrinsic size for each exact induced side. The two ordinary old-side maps therefore protect closed irreducible source tests. Their vertex counts are at most \(j_0\) by Step 2, so the checked closed-rank-\(j_0\) two-ordinary-side A-boundary gluing theorem produces appropriate completions of the projected closed side hulls. Strong K-amalgamation over the SINGLE generated closed K-root from Step 4, combined with the *actual source free cover* from Step 1, completes the ORIGINAL weak \(F\).

The Lean proof of this proposition is the now merged native2019_two_copy_tuple_localized_weak_completion (PR #172), using the pairwise root theorem from merged PR #169. The published-Picture full-source-protected-to-weak-source-ordinary interface is addressed separately by PR #173. \(\square\)

## 3. A precise obstruction: two transverse lines need not be a free cover

Even disjoint parameter-coordinate sets do not imply Step 1 automatically.

Take \(A\) to be a singleton with a loop and \(D=\{0,1\}\) with the reflexive binary relation \(0\le1\). Both singleton maps to \(0\) and \(1\) are full induced letters. In the coordinatewise two-coordinate power \(D^2\), take genuine transverse lines
\[
                         \ell_0(x)=(x,0),\qquad
                         \ell_1(y)=(1,y).
\]
Their parameter-coordinate sets \(\{0\}\) and \(\{1\}\) are disjoint. The vertices \(z=(0,0)\) and \(w=(1,1)\) lie in the first line only and second line only, respectively. Yet the coordinatewise relation \(z\le w\) holds. Thus one PURE CORE relation tuple crosses the two exclusive line-image pieces. Their literal induced union is NOT a free relational amalgam.

This is a mathematical counterexample to the *shortcut*, not to the corrected Ramsey theorem. The Lean Bool-power regression from PR #170 checks it independently. Upstream docs/theorem218-multiline-pairwise-overlap-audit.md gives an additional three-line example: two pairwise A-word overlaps with one line need not lie together in ONE word A-copy.

There is, by contrast, a valid free decomposition of the **whole native attachment** into a chosen attached old-copy range versus the REST excluding that copy's private exterior. The exact inverse images of these two sets under a positive source map form a free source cover (merged #137); relation tuples inside the power core belong to the REST, so they do not violate that valid cut. The difficulty shifts to constructing the ordinary old REST map and preserving a single closed boundary.

## 4. Attempted unrestricted proof of Lemma 2.30: established steps and OPEN arrows

The following is a detailed proof plan, **not** an unconditional proof.

**A. Base and easy original-source branches (verified).** In a closed B-covered Picture, any EXACT WEAK test of intrinsic \(\mathcal U\)-size at most one is completable by fully embedding its ambient closed hull into B (Lean #167). More generally this works whenever it possesses an ordinary irreducible intrinsic generating seed (Lean #168). The original weak tested carrier is never replaced in the conclusion.

**B. Finite active native history (verified).** Under the actual relatively U-closed attaching support assumption, every private-active native copy index has a source generator witness even for a NONINJECTIVE positive projection, so \(|\operatorname{Active}(F,p)|\le\operatorname{USize}(F)\) (Lean #160–161). In intrinsic rank at most two, a no-common-coordinate active set is exactly a transverse pair (Lean #171). Empty private-active history is completable through the core into A, at any intrinsic rank (Lean #154–157). A common active parameter coordinate yields an ordinary map to Old; a genuine vertex collision lets the previous weak-size invariant complete a maximal-rank exact test (Lean #151).

**C. Genuine general copy/rest free cut (verified).** At any selected old-copy index i, the actual native attachment has a free relational cover into that copy versus REST. A positive source map pulls it back to a free cover of the original exact tested vertices (Lean #137). Two distinct active private copies guarantee PROPER source sides (Lean #142), but absolute side vertex budgets follow only for weak sources on at most \(j+1\) vertices. A closed rank-\(j+1\) source may have arbitrarily more vertices than its generator rank.

**D. The REST map in three-or-more-line histories (OPEN G1).** If all other SOURCE-ACTIVE lines share a parameter coordinate k, evaluation of the complementary native subattachment at k and identity on old attached exteriors supply an ordinary REST map (Lean #138, #146). However, choosing a MINIMAL noncommon-coordinate subfamily and removing one exceptional index may leave omitted ORIGINAL ACTIVE line indices. Nothing proves their REST source vertices have a common coordinate. One must handle the whole active history recursively, or use a stronger completion invariant.

**E. Root compatibility for an actual copy/rest cut (OPEN G2).** A constant coordinate of an exceptional HJ line produces one true A-letter factorization on the overlap (Lean #134), but the chosen attached copy's inverse old map can take root vertices to arbitrary SUPPORT vertices of D. Agreement of outer parts does not imply they all lie in ONE old induced A-copy. The pairwise theorem #169 resolves this only when both side source images lie inside TWO genuine transverse attached copies. The other side of an arbitrary native copy/rest cut need not do so. Full vertex-exact compatibility remains unproved.

**F. Closure and ranks of projected side hulls (OPEN B1).** For a nonclosed attaching support the full native core and copy-complement rest may fail to be relatively U-closed. A positive source copy/rest FREE relational cover does not imply that the two induced pieces of an arbitrary closed source are themselves closed. Moreover, even if proper on tested vertices, a closed source of generating rank \(j+1\) may have many vertices. One must prove projected closed side hulls have rank at most j, including the COST OF THEIR COMMON CLOSED ROOT. Deleting an essential source generator only works under an explicit closure-saturated containment, not for an arbitrary copy/rest cut. This is documented by the upstream rank-budget and nonclosed-rest audits.

**G. The recursive invariant (OPEN I1).** The older weak-size successor conditional on the stronger OLD closed-rank invariant \(R_j(D)\) cannot be iterated as if it assumed only \(W_j(D)\). The uniform rooted \(W_j^{\mathcal K}\) invariant has a genuine zero base, monotonicity and SAME-RANK preservation along any established protected map, and it gives exact weak \(j+1\)-test completions if a GLOBAL protected map into the old closed B-covered Picture exists (Lean #163–166). The real mixed HJ successor has no such map in general, so **promotion** \(W_j^{\mathcal K}\to W_{j+1}^{\mathcal K}\) remains OPEN.

These are mathematical hypotheses still to be proved, not Lean elaboration errors. Neither this note nor the CI-green partial lemmas proves the unrestricted printed Lemma 2.30 or corrected Theorem 2.18.

## 5. Lean work suggested by the English proof

First, formally characterize the source-specific condition in Step 1: for the literal induced copy-i/copy-j inverse-image sides, a genuine relational free cover is equivalent to (a) actual vertex coverage by these two sets and (b) localization of EVERY ORIGINAL relation tuple wholly into one side. The forward direction is already covered by the checked positive free-cover theorem; the reverse direction follows from IsFreeAmalgam.covers and IsFreeAmalgam.rel_iff. This prevents a false implication from line transversality.

Second, finish the paper-faithful PR #173 bridge from the closed full protected Picture projection to a particular exact weak tested source. Its source vertex and tuple-localization hypotheses remain explicit and must not be dropped.

Third, attack the real mathematical gap: for a general native source with core-crossing tuples, construct a ROOTED decomposition whose shared closed K-boundary and projected generating-rank budgets are verified, or prove a compatible stronger relative-rooted completion successor. A finite list of active indices or pairwise A-word intersections is not enough to justify this step.

**Conclusion:** Section 2 gives a complete, already Lean-verified restricted two-copy lemma. Sections 3–4 are an explicit adversarial audit of why the current proof does not extend automatically. The remaining theorem is the invariant-preserving completion of arbitrary genuine native active histories, especially core crossings and their closed K-boundaries.
