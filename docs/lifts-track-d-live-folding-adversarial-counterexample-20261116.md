# Adversarial English audit: live folded profiles need not be finite

16 November 2026. This is a counterexample to an INTERMEDIATE COMPRESSION LEMMA, not a counterexample to the full lift theorem. No new Lean declaration is asserted.

## 1. Family satisfying the original scope

Use two symmetric irreflexive binary colours E_r,E_b and a unary mark M. For each i≥3 let H_i be a red K_i and a blue C_(2i+1) meeting at exactly one vertex x=v_0. Write the blue cycle as v_0,v_1,…,v_(2i),v_0. Replace each vertex by an independent fibre of i vertices and each coloured edge by the complete bipartite relation of the same colour between its fibres. Mark exactly the fibre above x. Call the resulting 3i²-vertex structure F_i. Add the one-vertex structure F_bullet with M true and both binary loops false. Let F^M={F_bullet}∪{F_i:i≥3}, with full-isomorphic copies.

Every member is finite and connected. Removing fewer than i vertices from F_i leaves each fibre nonempty, and connectivity of the base connects all remaining fibres and all vertices within them. Therefore no separator of size below i exists. For any fixed positive root width n, only finitely many i≤n can contribute minimal-cut pieces. Each finite F_i has finitely many such rooted pieces up to full rooted isomorphism. F_bullet has none. Thus F^M is regular in the printed per-width sense.

Every original source contains a full F_bullet. Since a singleton is irreducible, ANY EHN map out of a source embeds that marked loopless singleton fully in its target. Hence the exact printed tuple-surjective forbidden-image condition holds, even without tuple surjectivity.

This family is redundant. Its forbidden-free class is exactly Forb_EHN({F_bullet}). In unrestricted relational targets, a marked vertex with a red or blue loop need not contain this FULL singleton; the shorthand 'no marked vertices' applies only when targets are loopless. All entirely unmarked targets are allowed, which is sufficient below.

## 2. Live original minimal-cut pieces

Let R_i be the union of the two unmarked fibres above v_1 and v_(2i), of size 2i. After deletion, let C_i be the component on the fibres above v_2,…,v_(2i−1). The other component is the red part containing the marked root fibre. Both components have external neighbourhood exactly R_i. Restoring any one vertex of R_i reconnects them. Consequently R_i is a genuine minimal separating cut, not merely an arbitrary closed set.

The rooted induced pattern P_i on R_i∪C_i is the independent i-blow-up of the blue path v_1,…,v_(2i), of length 2i−1, with the entire endpoint fibres as its ordered root. It is a genuine minimal-cut piece of ORIGINAL F_i. It has no marked vertices, no red edges and no loops. Its Gaifman graph is bipartite; its nonempty irreducible full tests are singletons and blue edges.

Define the effective unary observation phi_i(a) to mean: P_i has an EHN realization with ALL 2i source-root coordinates mapped to a. This is allowed in the raw folded component expansion, and illustrates why source root width and the number of distinct target roots cannot be conflated.

## 3. Exact threshold on allowed structures

For j≥3 let B_j be an entirely unmarked blue cycle of length 2j−1, with root a_j. Each B_j is allowed. Then

    B_j satisfies phi_i(a_j)  iff  j≤i.

Necessity: choose one vertex from each successive source fibre. Their images form a blue closed walk of odd length 2i−1 rooted at a_j. Every odd closed walk contains an odd cycle of no greater length, by repeatedly splitting at repeated vertices and retaining an odd subwalk. The target has odd girth 2j−1. Thus j≤i.

Sufficiency: traverse B_j once and insert i−j immediate two-step backtracks. This gives a rooted closed walk of length 2i−1. Map each whole source fibre to its walk vertex. Positive blue edges are preserved. Every full singleton reflects M and the false loops; every blue source edge embeds as a blue edge with red false. Those are all nonempty irreducible tests, so the map is EHN.

In particular every phi_i is LIVE, witnessed by B_i. For i<k the allowed target B_k satisfies phi_k but not phi_i. Hence there are infinitely many semantically inequivalent LIVE folded observations over the SAME unmarked loopless singleton old root.

## 4. The rejected lemma

The statement

    regular + printed image closure
      => finitely many semantic types of LIVE folded observations
         on each fixed finite target root

is FALSE, even in this finite relational language, even for actual original minimal-cut pieces. Dead-predicate removal is sound but does not solve precompactness. This counterexample is stronger than merely observing that raw full-range EHN saturation can destroy regularity: the distinguishing patterns here have no forbidden marked core and really occur in allowed structures.

## 5. Why this does not rule out maximal-profile compression

Attach a new entirely unmarked blue triangle to any allowed witness over its displayed unmarked loopless singleton a. This is an allowed full extension: no new forbidden marked loopless singleton appears and all old relations/loops remain unchanged. The triangle has closed odd walks of every odd length at least three, so the extension realizes ALL phi_i(a), i≥3, simultaneously.

Therefore every witness already maximal on a must make every phi_i true. This proves collapse of the DISPLAYED infinite sequence in maximal witnesses, not uniqueness of all raw maximal profiles. The example does not show infinitely many maximal root profiles or nonexistence of a precompact lift of its trivial shadow class.

The full-strength route should therefore seek a cofinal coherent compression of maximal profiles from the ORIGINAL assumptions. Finiteness of all pre-maximal live observations is too strong. Finite stable codes, cofinality, restriction/re-enumeration coherence, and transfer adequacy must still be proved, not added as hypotheses and called the original theorem.

## 6. Independent validation after the mathematical proof

For i,j from 3 through 6 the new checker confirms the lower-triangular threshold matrix; ten positive folded maps; all 16 triangle-extension maps; 6,848 full singleton/edge tests; 36 restorations of one cut vertex; and all 18,852 vertex-deletion tests below the blow-up parameter for i=3,4. It verifies triangle-freeness of each source path-blowup before treating singleton/edge tests as exhaustive. Both the original marked family and the unmarked live pieces are kept explicit.

These finite checks catch indexing and EHN-reflection mistakes; they are not the infinite proof, which is the argument above. No native Lean model of this new infinite live-profile counterexample is claimed. The English source-preserving transfer proof is in the companion note; the frozen numbered manuscript is untouched.
