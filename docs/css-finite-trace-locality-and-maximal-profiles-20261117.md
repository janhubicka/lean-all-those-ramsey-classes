# Finite HE homogenization, bounded trace consistency, and the infinite-profile criterion

**17 November 2026. English proofs and executed bounded regressions. Not Lean-certified.**

This continues the CSS comparison and replaces no frozen manuscript text. These are alternative, deliberately richer trace lifts, not a claim that the original minimal-separator/distinct-root lift is correct. The finite theorem is relational and uses no forbidden-image-closure assumption. The infinite criterion is proved separately; its additional finiteness condition is NOT inferred from printed per-source-width regularity. No Ramsey or optimal-arity conclusion is claimed.

## 1. Setting and finite statement

Let L be a finite relational language with positive arities. All embeddings and induced substructures are full. A homomorphism-embedding (HE map) is a positive homomorphism whose restriction to every intrinsically irreducible induced source substructure is a full embedding. Irreducibility is computed in that induced source, not an ambient Gaifman graph.

Let F be a finite family of finite nonempty connected L-structures, K=Forb_he(F), and N=max({1} union {|F|:F in F}).

**Finite theorem (English proof).** There is a finite relational lift language L+ and a finitely bounded Fraisse class C_max with exact finite shadows K_fin, strong amalgamation with free old-language shadows, a forbidden-full-embedding description on at most N vertices, and added predicate arities at most N. Repeated target-root coordinates are allowed. Its limit has an omega-categorical universal reduct for countable K, in the nontrivial case. The expansion is definitional; its predicates and their complements are existentially definable in the reduct. Consequently the reduct theory is model-complete and is a model companion of the universal avoidance theory.

If K contains only the empty structure, use the trivial interpretation. Empty F needs no new predicates. Nullary relations require one fixed nullary diagram for joint embedding; functions are outside the theorem.

The new strengthening beyond the preceding CSS note is finite boundedness and the justified passage from arbitrary traces to maximal traces. The arbitrary-trace limit need not be existentially complete: for triangle-free graphs it can retain an isolated-vertex type, whereas the maximal-trace limit cannot.

## 2. Trace vocabulary and finite witnesses

For every nonempty connected induced substructure P of a member of F, and each ordered nonempty tuple r of distinct source vertices, introduce Q_(P,r). Retaining labelled duplicates is harmless. Underlying patterns are closed under connected induced substructures.

For any old structure W define

    Q_(P,r)^Tr(W)(a) iff there is an HE map h:P -> W with h(r)=a.

Target entries of a MAY coincide. Let C_raw be all finite induced substructures of Tr(W), W in K.

Every finite raw member A* has a finite witness: select a finite HE image for each true trace atom on A and restrict the original witness to their union with A. Full restriction preserves the selected true atoms and cannot create a false one.

Put T(k)=sum_Q k^(arity(Q)), summing over the added predicates. A feasible profile on k vertices therefore has a witness with at most k+N T(k) vertices.

## 3. One-way source transfer

**Lemma.** Let allowed A,B meet in a common full substructure X. Suppose every positive trace on X in Tr(A) holds in Tr(B). For the free old-language amalgam D=A+_X B,

    D in K, and Tr(D)|B=Tr(B).

If root traces are equal, both sides' entire traces are preserved.

**Proof.** Fix a connected source pattern P and an HE f:P->D with a nonempty distinguished root tuple mapped into B. Write V_A=f^-1(A), V_B=f^-1(B), R=f^-1(X). No positive source tuple meets both V_A\R and V_B\R: its image would cross private target sides.

Each connected component C of the INDUCED structure P[V_A] containing an A-only source vertex meets R. Otherwise it has no tuple connection to the remainder of the connected source, which has a root vertex mapped into B. The pattern P[C], rooted at all of C intersect R, is on the trace list. Its map into A gives a trace on a tuple in X, including any repeated coordinates. Trace inclusion supplies an HE g_C:P[C]->B with precisely the same root tuple.

Retain f on V_B and use g_C off R. The maps agree on overlaps. Every positive source tuple lies in one retained/transferred source part. Every irreducible INDUCED source test lies in V_B or one transferred component: opposite private sides yield a proper free decomposition, as do separate components of P[V_A]. Thus the combined map is HE and preserves the original distinguished root tuple. Reverse trace inclusion uses the full embedding B->D.

For forbidden-freeness, an HE F->D either has image entirely in A, already impossible, or has a vertex mapped into B. Root F there and transfer it into B, again impossible. QED.

No injectivization, source replacement, new forbidden pattern, support-minimum assumption, or image-closure premise occurs. Full negative information is checked only on the genuine irreducible source tests. Root coordinates are retained literally.

## 4. Maximal profiles

Fix a finite old A in K. A feasible profile over A is the set of all trace atoms on A realized in some allowed full extension W. Order profiles by inclusion, fixing the old structure.

**Lemma.** Tr(W)|A is maximal under allowed extensions of W iff its profile is an inclusion-maximal feasible profile over A.

Only the converse needs explanation: if W' realizes a strictly larger profile over A, rename outside A and use the one-way lemma on W+_A W'. This gives an actual allowed extension of W realizing the added atom.

For finite F there are finitely many atoms on A, so every feasible profile extends to a maximal one; finite witnesses suffice. The one-way lemma also makes this maximalization extend a previously specified witness.

**Hereditary maximality.** A maximal A-profile restricts to a maximal profile on every X subset A. Otherwise glue its witness to a witness of a larger X-profile; the resulting allowed extension increases the A-profile too.

Let C_max consist of raw lifts whose entire-carrier profiles are maximal. It is hereditary. To amalgamate, take maximal witnesses of two finite members, rename them to meet on their common finite expanded root, and freely amalgamate the witnesses. Equal root profiles preserve both witnesses' traces. Maximize on the finite union of the specified carriers. No side profile changes, since its witness was already maximal there. Restriction gives strong amalgamation with free old shadow.

Connectedness gives joint embedding via disjoint union and maximalization. Exact shadows follow by maximizing over any allowed finite old structure.

## 5. The finite local-to-global theorem

**Theorem.** A finite expanded structure A* belongs to C_raw iff every induced substructure on at most N vertices belongs to C_raw.

Necessity is hereditary. For sufficiency choose, for every nonempty Z subset A with |Z|<=N, a finite allowed witness W_Z with

    Tr(W_Z)|Z=A*|Z.

Rename the private vertices so each witness meets A exactly in Z, and different witnesses meet only at their prescribed base overlaps. Form D from the old base A and these witnesses by taking the union of their positive old tuples. No tuple joins private vertices of different witnesses, or a private witness vertex to a base vertex outside its root. All base/witness inclusions are full.

We now prove D is allowed and Tr(D)|A=A*. These are conclusions, NOT assumptions about simultaneous witness compatibility.

### Central-witness transfer

Let P be a connected source pattern and f:P->D HE with image meeting A. Set Y=f(P) intersect A. Since |P|<=N, the nonempty set Y has size <=N, so W_Y is one of the attached witnesses.

Keep f on R=f^-1(A), interpreting its image Y inside W_Y. For each W_Z take each connected component C of the induced structure P[f^-1(W_Z)] containing a source vertex mapped privately into that witness. Such a component meets R, by connectedness and absence of private cross-tuples.

The rooted pattern P[C], with root C intersect R, belongs to the trace vocabulary. Its original map into W_Z yields a trace on a tuple in Z intersect Y. Both W_Z and W_Y induce the prescribed A* on their roots, so the same trace holds in W_Y. Choose an HE map P[C]->W_Y fixing exactly those original source-root images.

Combine these maps with the retained map on R. Every positive tuple lies in one part. Any irreducible source test containing a private image lies in one witness-preimage component; a test wholly in R is handled by the full embedding A[Y]->W_Y. The combined map is HE and agrees with f on ALL source vertices originally mapped into A. Collisions introduced between different transferred components do not matter: no irreducible source test spans their private parts.

### Exact traces and avoidance

Every true atom of A* has a witness in W_Z where Z is its tuple support. Conversely, any atom realized in D on a base tuple transfers to W_Y as above while fixing that tuple, so was already prescribed in A*.

A forbidden HE map whose image meets A transfers to an allowed W_Y. A forbidden HE map whose image misses A lies wholly in one witness, by source connectedness. Both are impossible. Therefore D is allowed and its induced base trace is exactly A*.

### Explicit bound

For n=|A|, choosing the witnesses by Section 2 gives

    |D| <= n + N sum_(k=1)^min(N,n) binom(n,k) T(k).

For fixed F and L this is a polynomial bound in n. It is not claimed optimal or practical.

## 6. Finite boundedness of the maximal age

**Corollary.** A* is in C_max iff every restriction to at most N vertices is in C_max.

Small maximal restrictions first imply global raw feasibility by Section 5. Any strictly larger global feasible profile adds an atom supported on at most N vertices, contradicting maximality on that support. Conversely, global maximality restricts by Section 4.

Thus C_max=Forb_e(B_max), for the finite list of nonmembers on at most N vertices. The list is effective: on each small old carrier enumerate allowed witnesses up to k+N T(k), compute feasible profiles, and retain the inclusion-maximal ones.

This is not an ordered Ramsey/local-completion proof. The old reduct of the amalgam is free, but additional lifted relations can acquire cross-tuples. The full expanded class is NOT being asserted to be a free-amalgamation class.

## 7. Generic reduct and model-completeness

Let U* be the Fraisse limit of C_max. Any countable allowed input can be extended by a fair countable sequence of allowed witness additions to have maximal traces on every finite subset. Its lifted age lies in C_max, so it embeds into U*. The old reduct U is allowed, because a forbidden HE witness would have finite image in an allowed finite lifted member. This proves countable universality.

The predicates of U* equal the actual traces of U. For a named positive atom, take a maximal witness of its finite parameter structure, include a finite realizing HE image, maximize over the resulting larger finite carrier, and use the limit extension property. The earlier parameters remain unchanged by maximality. Conversely, an actual HE map into U has finite image; an allowed witness of the lifted image structure realizes the same query on the same parameter profile.

Each raw trace query is existential in the old language: use all positive source tuples and the full atomic diagrams and inequalities of its irreducible source tests. These formulas use negation and are not asserted primitive-positive.

For a fixed finite old parameter diagram the maximal profiles form a finite antichain. To define one profile t among them, choose a positive query in t\u for each other maximal profile u. Their finite conjunction, together with the full old diagram/equality pattern, isolates t. Consequently each added predicate AND its complement is existentially definable in U. Quantifier elimination in the finite relational homogeneous expansion yields model-completeness of Th(U).

Every finite allowed structure embeds in U. Compactness of full atomic diagrams therefore embeds every model of the universal avoidance theory into a model of Th(U), while Th(U) implies avoidance. Hence Th(U) is a model companion. The expansion is definitional and Aut(U)=Aut(U*).

These are English derivations for the richer finite HE lift, not identifications with the original minimal-piece construction.

## 8. Infinite families: maximal folded profiles give an exact criterion

Allow arbitrary F of finite nonempty connected structures in the same finite relational language, taking countably many isomorphism representatives. Keep ALL connected induced source patterns and ALL nonempty source roots; target roots may fold. The raw vocabulary is countable but need not be finite.

For finite old A, write M(A) for the inclusion-maximal feasible complete raw profiles over A, realized in countable allowed witnesses. Profiles may have infinitely many atoms. Countable witnesses lose no information, since there are countably many queries and every true query has a finite witness.

### Cofinal existence

Enumerate the raw queries on A in a countable allowed witness. Whenever a false query can become true in an allowed extension, take such an extension, using countable extraction. Otherwise leave the witness unchanged. The full increasing union remains allowed: a forbidden HE witness has finite image and would occur at a finite stage. Every omitted query was impossible over an earlier stage. The union is extension-maximal on A and, by one-way gluing, inclusion-maximal in the profile poset. Hereditary maximality still holds.

### Criterion (English proof)

The following are equivalent:

(a) K_fin admits a hereditary precompact relational Fraisse lift with exact old shadows.

(b) M(A) is finite for every finite A in K.

Under (b), the lift can have strong amalgamation and free old shadows.

**Sufficiency.** For each labelled finite old A and t in M(A), add an |A|-ary predicate naming the entire profile on injective enumerations of A; set these predicates false on repeated-coordinate tuples. There are finitely many added symbols per arity. These labels encode complete raw folded information, including queries with arbitrarily large source roots, BEFORE repeated-coordinate tuples are discarded in the new coding language.

Take finite traces of witnesses maximal on the specified carriers. Maximality restricts, so heredity holds. Matching expanded roots means equality of their complete raw profiles; one-way transfer in both directions gives allowed witness amalgams, and maximalizing on the finite union preserves both sides. Joint embedding and exact shadows follow as before. Only arities up to a finite carrier's size can contribute, so the expansion is precompact and the age countable. Its limit is oligomorphic. Fair maximalization over all finite parameter sets of a countable old input proves countable universality.

**Necessity.** For each t in M(A) choose a countable allowed witness W_t. Precompactness and exact finite shadows provide a coherent lift of W_t: enumerate its finite initial segments and apply the finitely branching tree argument to their nonempty finite sets of possible lifts, using hereditary restriction.

If distinct t,u received the same labelled expanded type on A, embed their countable lifts in the given lifted Fraisse limit and align the finite roots by homogeneity. Its old reduct is allowed, since every finite substructure is allowed. It would realize a feasible profile containing both t and u, forcing t=u by maximality. Therefore

    |M(A)| <= number of labelled expanded types over A,

which is finite by precompactness.

### Precise boundary

The condition is finiteness of MAXIMAL FEASIBLE PROFILES, not finiteness of all raw folded queries or nonmaximal profiles. Infinitely many observations can become jointly true in an allowed extension. Permanent incompatible choices cannot.

For the candidate infinite decorated-half family, distinct binary choices yield distinct maximal singleton profiles; conditional on the separately audited infinite construction, |M(X)|>=2^r for every r. No proof that the original per-source-width regularity implies finiteness of M(A) is asserted here. The concrete family hypotheses of that counterexample remain a separate Lean-validation obligation.

## 9. Verification boundaries and executed checks

The proofs retain induced rather than ambient components, complete irreducible source tests, the identical source and literal repeated boundary tuple. They use neither arbitrary weak-image injectivization nor inherited extremal assumptions. The local-to-global construction controls negative as well as positive traces. The maximal pass, not the raw age alone, supports the model-completeness assertion.

The accompanying standard-library-only checker is independent of the prior scripts. Executed results:

- 1,043 binary/ternary source tables; 46,064 compatible base/private-region assignments;
- 49,398 transferred components and 450,705 induced irreducible-test containment checks;
- 2,083 enumerated coloured targets, 1,986 avoiding the finite diagnostic forbiddens;
- seven profiles among those BOUNDED singleton models; 84 same-profile amalgams;
- 7,506 preserved positive side-trace instances and 345 noninjective pattern maps;
- 86 local witness covers on four-vertex triangle-free bases with N=3 and 14 roots each;
- all covers preserved exact traces and avoidance; 41 used the explicit maximal profiles.

The seven bounded-model profiles are not claimed to enumerate all feasible profiles. Triangle-free maximality is separately elementary: adding a fresh leaf never creates a triangle, so the existential neighbour flag must be true at every vertex in a maximal profile.

All assertions passed. These bounded tests do NOT certify the unbounded theorems. No Lean declaration, frozen manuscript text, validation marker, or theorem certification is changed by this note.

## 10. Literature comparison

Hubicka--Nesetril, *Homomorphism and embedding universal structures for restricted classes*, arXiv:0909.4939v2, Theorem 1.3 (p. 5), states finite bounded homogenization/model-completeness for ordinary forbidden homomorphisms. The HE conclusions above are derivations here, not quotations from that theorem.

*Universal structures with forbidden homomorphisms*, ITI 2012/565, Definition 2.3 (p. 10), uses finitely many piece classes in total. *All those Ramsey classes*, arXiv:1606.07979v4, Definition 3.13/canonical lift (p. 40), uses finiteness separately at each source width and distinct target-root coordinates. Those two rendered definition pages were inspected in this continuation.
