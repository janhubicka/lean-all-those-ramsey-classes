# Full-strength counterexample candidate: locally finite closures do not ensure precompactness

16 November 2026. **English proof, adversarially audited and checked in finite instances; not Lean-certified. Independent mathematical review is required before changing the frozen manuscript.** No new Lean declaration or manuscript edit accompanies this note.

## Claim and exact target

There is a finite RELATIONAL signature L and an infinite family F of finite connected structures which is regular in the printed PER-WIDTH sense and satisfies the printed TUPLE-SURJECTIVE EHN image-closure condition, but K=Forb_EHN(F) has infinitely many allowed structures rooted at the same singleton, no two amalgamable over that root. Hence K has no hereditary same-carrier precompact RELATION-ONLY expansion with amalgamation; no omega-categorical member universal even for its finite members; and its marked singleton has infinite Ramsey degree.

All native closures are the identity: cl(A)=A. Thus even a uniform closure-size bound f(n)=n does not remove the obstruction. This is not merely nonregularity of raw saturation or live profiles that collapse after maximalization. The rooted incompatibilities persist under every allowed extension. It does not contradict the finite-family corollary or a globally FINITE-TOTAL-piece-class definition of regularity. The additional weak-order/completion-locality hypotheses of the separate ordered Ramsey theorem are not verified here; the target is the earlier full homogenizing-lift statement.

## 1. Language and the finite triangle family

L has binary R,B, unary M, and ternary T. In all constructed sources, R is a simple symmetric red graph, B is directed and contained in R, and T is empty. Thus source Gaifman adjacency is precisely R. If R is triangle-free, all nonempty irreducible full source tests are singletons and red edges.

Let C be the finite family of all red K3 structures, with arbitrary unary M subset, arbitrary B subset of the six off-diagonal ordered pairs, and T empty. There are at most 512 labelled possibilities. Each is irreducible, so an EHN map from it must be a full embedding of the whole structure.

## 2. Explicit triangle-free strips

For k>=3 take independent sets

Z={z_0,...,z_(k-1)}, U={u_1,...,u_(k-1)}, V={v_1,...,v_(k-1)}.

Define the graph J_k by exactly these edges:

    z_r -- u_a iff a<=r;
    z_r -- v_b iff r<b;
    u_a -- v_b iff b<=a.

A triangle would require b<=a<=r<b, impossible. There are 3k-2 vertices. Each root z_r has degree k-1; each private u_a,v_b has degree k.

**Separator lemma.** Every vertex separator of size s satisfies 3s>=k-2. If s>=k-1 this is immediate. Otherwise every surviving component has minimum degree d>=k-1-s>=1. In a triangle-free graph the two endpoints of an edge have disjoint neighbourhoods, so every such component has at least 2d vertices. Two components imply

    3k-2-s >= 4(k-1-s),

which rearranges to the stated bound.

**No-collapse pairs.** Every pair of distinct vertices of Z is joined by a three-edge path: for r<s use z_r,v_(r+1),u_(r+1),z_s. Every two distinct vertices of U union V are either adjacent or joined by a three-edge path:

    u_a,z_a,v_(a+1),u_c          for a<c;
    v_b,u_b,z_b,v_d              for b<d;
    u_a,v_a,u_b,v_b              for a<b.

The last line covers the nonedges u_a v_b; the other cross-pairs are edges. A homomorphism into a loopless triangle-free red graph cannot identify the endpoints of an edge or a three-edge path.

## 3. Allowed rooted cycle witnesses

For each odd t>=5 define A_t on 0,...,t-1:

* M={0}; call the marked root x=0.
* B is the directed cycle 0->1->...->t-1->0.
* R is complete tripartite with parts {0}, the odd positions, and the nonzero even positions.
* T consists of ALL ordered triples of pairwise distinct vertices.

Every blue arc is red. The full singleton at x is identical for every t: marked, no binary loops, no repeated ternary tuple. A red triangle core from C cannot map EHN into A_t because its empty T would have to be reflected on three distinct target vertices. The same holds in D_(p,q)=A_p free-amalgam_X A_q: every red triangle lies in one side and has a positive T tuple there.

## 4. A high-connectivity source for each distinct pair

For odd 5<=p<q put k=p+q+3. Form the red graph of S_(p,q) by gluing two copies of J_k along all k roots Z, with disjoint private sets (U^p,V^p) and (U^q,V^q). Mark precisely Z; put T empty. It is triangle-free, has 5k-4 vertices and 3k(k-1) red edges.

If deleting s vertices has 3s<k-2, each copy remains connected by the separator lemma, and a common root survives since s<k. The double strip remains connected. Thus every separator of the double strip has 3s>=k-2.

For t=2r+1 in {p,q}, define g_t from its strip to A_t by

    g_t(z_a)=0;
    g_t(v_b)=2b-1 for b<=r, and 1 otherwise;
    g_t(u_a)=2a-2 for 2<=a<=r+1, and 2 otherwise.

The indices exist because k>=r+2. Private V maps to odd target positions, U to even positions, so every red source edge maps to a red target edge.

Define B on each strip as the pullback of B^(A_t) RESTRICTED TO EXISTING RED SOURCE EDGES. That is, B(a,b) iff R(a,b) and B^(A_t)(g_t(a),g_t(b)). No source blue arcs are added outside the red graph. The common root has no red edges, so the two definitions agree there.

The source contains the distinguished directed blue path

    z_0,v_1,u_2,v_2,u_3,...,v_r,u_(r+1),z_(k-1),

of length t. Its endpoints are marked and distinct; all internal vertices are unmarked. Its g_t-image goes around A_t exactly once.

The two g_t combine to a vertex-surjective EHN map S_(p,q)->D_(p,q), folding every source root onto x. Positivity holds; all irreducible source tests are singletons or red edges; M and all binary truth values reflect on those tests by construction; T is false on target tuples using at most two vertices. This map is NOT tuple-surjective, since D_(p,q) has positive ternary tuples absent from the source.

**Length test.** An EHN map S_(p,q)->A_t would send both distinguished paths to directed closed walks at the unique marked vertex with no internal marked visit, since singleton tests reflect M. In a directed t-cycle such a walk has length EXACTLY t, not merely a multiple of t. Hence p=t=q, impossible. More generally, S_(p,q)->D_(r,s) EHN forces {p,q}={r,s}.

## 5. The original forbidden presentation and printed image closure

For each pair p<q let H_(p,q) contain, up to full isomorphism, all finite red-triangle-free structures H for which there is a VERTEX-SURJECTIVE and TUPLE-SURJECTIVE EHN map S_(p,q)->H. These are generated images, not full-range saturation allowing extra tuples. Each has |H|<=5k-4, a symmetric loopless R, B subset R, T empty, and connected red graph. For each fixed pair there are only finitely many isomorphism types. Identity ensures S_(p,q) itself is a member.

Set

    F = C union all H_(p,q), for odd 5<=p<q,

including all isomorphic copies. All members are finite, nonempty and connected.

**Printed closure proof.** Let H in F map tuple-surjectively and EHN into any target E; vertex-surjectivity of this latter map is NOT assumed. If H is a triangle core, it embeds fully, so E contains a forbidden member. Otherwise compose S_(p,q)->H->E. EHN and tuple-surjectivity both compose. Restrict E fully to the finite actual image J; in this RELATIONAL language the factor is vertex-surjective, tuple-surjective and EHN. T^J is empty, R^J is symmetric loopless, B^J subset R^J. If J has a red triangle, its full three-vertex structure is in C. If not, J belongs to H_(p,q). Either way E contains a FULL original forbidden member, exactly as required by the printed hypothesis.

## 6. Regularity after taking generated images

Let q:S_(p,q)->H be EHN with H red-triangle-free. The no-collapse paths prove that q is injective on Z, on U^p union V^p, and on U^q union V^q. Full singleton reflection of M prevents a marked root from colliding with a private unmarked vertex. Thus every fibre has size at most TWO (a marked fibre has size at most one).

If Y is an n-vertex separator of H, its preimage separates the source: otherwise its connected complement would map onto the disconnected H minus Y. Hence

    |q^-1(Y)| <= 2n;
    3|q^-1(Y)| >= k-2;
    therefore 6n >= k-2 = p+q+1.

Consequently a genuine width-n piece can occur only for p+q<=6n-1. There are finitely many such pairs, finitely many quotients per pair, and finitely many rooted piece isomorphism types in each quotient. The triangle cores have no pieces. This proves FINITENESS OF ROOTED-ISOMORPHISM TYPES at each width, stronger than the printed finiteness of incompatibility-profile classes.

Indeed any forbidden member contributing a width-n piece has at most 5k-4<=30n+6 vertices. There are NO width-one or width-two pieces, since p+q>=12.

## 7. Persistent incompatible witnesses in the allowed class

Write K=Forb_EHN(F). Every A_t belongs to K: triangle cores are excluded by T, and a map H->A_t with H in H_(p,q) would compose to the impossible S_(p,q)->A_t.

Suppose A_p and A_q, p!=q, had ANY amalgam E in K over their marked root. It need not be free or strong; private images may overlap. Compose each strip's g_t with its full side embedding into E. These agree on Z. Every source positive tuple and every irreducible source test is in one strip, so the glued map S_(p,q)->E is EHN. This contradicts S_(p,q) in F.

Therefore (A_5,x),(A_7,x),(A_9,x),... are pairwise non-amalgamable over the identical old singleton.

This incompatibility cannot be erased by maximalizing. The first strip of S_(p,q) has a folded rooted realization in A_p but cannot acquire one in any allowed extension of A_q: combining it with the unchanged other strip realization in A_q would create a forbidden S_(p,q) map. Thus the root distinctions are persistent, unlike the previous live-profile example where one triangle extension made every displayed query true.

## 8. Consequences: actual theorem, not just one construction

**No precompact relational AP lift.** In any hereditary same-carrier relation-only expansion with exact shadow K, choose an expansion of each A_t. A singleton remains a full expanded substructure because only relations were added. Precompactness gives finitely many expansions of that same old singleton, so two different A_p,A_q induce an identical root expansion. Amalgamation in the expansion gives an allowed old amalgam, contradiction. This excludes EVERY such precompact relational amalgamation expansion, not just our component language.

This argument deliberately does not exclude expansions adding new functions which make the singleton nonclosed; that changes the substructure category and is not the relation-only lift promised in the original theorem.

**Original canonical failure.** Since F has no width-one or width-two pieces and the original added relations require injective tuples, its canonical profile on the singleton is always empty and maximal. Thus the A_t witness the same original maximal singleton lift, while their free amalgams are forbidden. This directly refutes the specified canonical amalgamation lemma as well.

**No omega-categorical universal member.** If an allowed countable U contains full copies of every A_t, their roots lie in different automorphism orbits: an automorphism aligning two roots would produce the forbidden amalgam inside U. Hence U has infinitely many singleton orbits and is not omega-categorical. The incompatibilities can also be expressed by mutually exclusive parameter-free existential formulas for full rooted A_t copies.

**Infinite singleton Ramsey degree.** Take r distinct lengths and B their disjoint union. B is allowed because every forbidden source is connected. In any C in K, colour a marked singleton copy by i when it supports a full rooted A_(t_i) copy, and otherwise by a fixed default colour in {1,...,r}. The colour is unambiguous because no vertex supports two of the chosen witnesses. Every B-copy sees all r colours. As r is arbitrary, the marked singleton has infinite Ramsey degree. A hereditary precompact relation-only Ramsey expansion would bound this degree by its finite number of singleton lifts, so it is impossible. This does NOT claim the separate weak-order/completion-locality premises of the ordered theorem hold for this presentation.

## 9. Removing full-substructure redundancy

Let F_min consist of the full-substructure-minimal members of F. Every finite F-member contains one by finite descent. Therefore Forb_EHN(F_min)=Forb_EHN(F). Printed image closure persists by first finding a full F-member in the image and then a minimal member inside it. Regularity persists here because F had finitely many ROOTED-ISOMORPHISM types of pieces at each width, a property inherited by subfamilies. Connectedness persists since retained members are original members.

Thus the counterexample survives removal of full-substructure redundancies and can be presented by a full-embedding antichain. This is not an assertion of minimality for arbitrary EHN maps. The example does not depend on adding a redundant marked singleton that trivializes the shadow.

## 10. Adversarial gates and independent checks

The decisive gates were checked separately: induced rather than ambient irreducibility; full unary reflection; full blue reflection on EVERY red edge (not only a displayed path); no extra T in tuple-generated images; arbitrary non-vertex-surjective closure targets; fibre-size control after generated-image closure; and impossibility of arbitrary amalgams rather than only free ones. A directed first-return test, not an odd-girth heuristic, proves the exact length constraint.

The complete English proof was written before finite validation. Two standalone scripts in the accompanying artifact bundle were executed:

1. `check_candidate.py`: six official pairs among 5,7,9,11 with k=p+q+3; six displayed surjective EHN maps; 6822 full singleton/edge tests; 8766 within-block pair certificates; 96 distinguished path edges; 162 target-red-triangle T-exclusions; 126 directed return-length tests. PASS.
2. `audit_geometry.py`: an independent circular-graph construction of J_k for k=4,...,10; exact connectivity k-1 of each strip and k of its double; 861 within-block pair identifications forcing a triangle/loop; 784 cross-private identifications for the (5,7) source, with 542 EHN quotients and 25 triangle-free EHN quotients; and an exhaustive 64-map matching-quotient family on a smaller strip. PASS.

These checks are not an exhaustive enumeration of all quotient partitions and do not substitute for the arbitrary-k/image proofs in Sections 2,5,6. No native Lean bridge or kernel certificate is claimed. The full proof, executable scripts, raw result JSON and hashes are supplied in the conversation artifact bundle.

## 11. Relation to the user's local-finiteness intuition

With c_n finite distinct-root symbols of arity n and |A|=a, the original counting bound is 2^(sum_(n<=a) c_n (a)_n). Finite closures make this a count on a finite old substructure. What fails is the claim that the needed corrected piece information still fits that finite effective codebook. Here every closure is literally itself, but large original source roots fold to one point and force infinitely many persistent root states.

Under the literal conventions audited, this is evidence against the full positive conclusion, not merely a failed proof strategy. A corrected positive theorem must explicitly prevent this phenomenon; stronger effective-root regularity or a stronger quotient/image closure may be appropriate, but no additional hypothesis is silently inserted here. The finite-family repair remains unaffected.

Statement anchor: `janhubicka/All-those-Ramsey-classes/ramsey.tex`, canonical lift and main lifting theorem, blob 652d73b8896ca9884cb9f040d59c4804d63b5823; published as Hubicka–Nesetril, All those Ramsey classes, Advances in Mathematics 356 (2019), 106791. The exact distinction between per-width regularity and finite-total regularity, and between tuple-surjective images and full induced images with added tuples, is essential.
