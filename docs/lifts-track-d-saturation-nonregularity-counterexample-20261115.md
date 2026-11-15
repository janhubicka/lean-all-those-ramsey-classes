# Full-range EHN saturation can destroy regularity

**15 November 2026.** Independent Track D adversarial audit. This is a mathematical obstruction to generalizing the finite-relational full-range-saturation repair of PR #1228 to *arbitrary infinite regular forbidden families*. The frozen numbered manuscript is unchanged.

## The theorem

There is a finite relational signature L with just **two symmetric, irreflexive binary relations** (red R and blue B), and a family F of finite nonempty connected L-structures, satisfying:

1. F is **regular** for the genuine 2019 global minimal-separator piece equivalence: at every fixed positive root width, the set of incompatibility-profile equivalence classes is finite.
2. The full-range EHN saturation G = FullRangeEHNSaturation F is **not regular**: it has infinitely many pairwise inequivalent forbidden pieces already with **one ordered root**.

Thus no unconditional theorem of the form “regular F implies regular Sat_EHN(F)” can repair the general regular infinite-family hypothesis. Connectedness and finiteness of the native relational language are already present in this counterexample. The bounded/uniform-size positive result in PRs #1228/#1247 is unaffected.

## The graph family

For each integer i >= 3, define H_i by taking:
- a RED clique K_i on i vertices;
- a BLUE odd cycle C_(2i+1) on 2i+1 vertices;
- identifying exactly one vertex x of these two graphs.

No edge is simultaneously red and blue; no loops. There are 3i vertices in H_i.

Let F_i be the **independent i-blow-up** of H_i: replace every vertex v by an independent fibre {v} x {1,...,i}; for every red/blue edge uv of H_i put all i^2 edges of the same colour between the corresponding fibres. Put no edges within any fibre. Thus |F_i| = 3i^2.

Set F = {F_i : i>=3}, with all full-isomorphic copies admitted.

Each F_i is connected, as H_i is connected and every base edge is replaced by a complete bipartite graph.

## F is regular

The minimum size of a separating vertex set of F_i is **i**.

Indeed, deleting fewer than i vertices from F_i leaves at least one vertex in *every* fibre. Each base edge is still realized between surviving vertices. Because H_i is connected, the remaining graph is connected. Conversely, deleting the entire size-i fibre over x disconnects the red and blue sides. Hence vertex connectivity equals i.

Fix any root width n. A genuine minimal separating-cut piece with n distinct roots in F_i requires n>=i. Hence only finitely many F_i contribute pieces at this width (namely 3 <= i <= n). Each such F_i is finite and has finitely many choices of a cut, component and root ordering. Up to a full root-preserving isomorphism of its induced piece, there are finitely many selected charts, hence at most finitely many incompatibility-profile classes. This proves regularity of F at every fixed positive width.

## Each H_i lies in the full-range saturation

The quotient q_i : F_i -> H_i collapsing every independent fibre to its base vertex is vertex-surjective and EHN.

Positive red/blue edges are preserved. In a binary relational language, an irreducible full source substructure is a Gaifman clique. Such a clique contains at most one vertex from each independent fibre; q_i is injective on it. On each pair of distinct clique vertices, red/blue truth values are exactly the pullbacks of those of H_i, including negative truth values; loops are false in both. Thus every irreducible test embeds FULLY. This proves H_i belongs to G.

The singleton {x} is a genuine minimal separating cut of H_i. Its components after deletion are the red K_(i-1) and the blue path on 2i vertices, both connected. Therefore the rooted RED K_i piece P_i (root x) and the rooted BLUE C_(2i+1) piece Q_i (root x) are actual selected width-one forbidden geometric pieces of G.

Every such piece has the identical full root structure: a one-point structure with no loops of either colour.

## Exact threshold for incompatible width-one pieces

For i,j >=3, let H_(i,j) be the FULL free amalgam over their shared singleton x of P_i and Q_j: a RED K_i and a BLUE C_(2j+1) meeting exactly at x.

**Claim: H_(i,j) belongs to G iff j<=i.**

*If j<=i:* Traverse C_(2j+1) once and pad by 2(i-j) steps of immediate backtracking to obtain a closed walk of length 2i+1 rooted at x that visits every vertex of C_(2j+1). It defines a colour-preserving, vertex-surjective graph homomorphism from the BLUE C_(2i+1) to the BLUE C_(2j+1), fixing x and mapping each source edge to a blue edge. Send the RED K_i identically to the RED K_i. These maps agree at x and together yield a vertex-surjective EHN map H_i -> H_(i,j): the only nontrivial irreducible source tests are red cliques and blue edges, and each is embedded fully on its image. Composing with q_i gives a vertex-surjective EHN map F_i -> H_(i,j). Therefore H_(i,j) belongs to G.

*Only if:* Suppose F_k -> H_(i,j) is EHN (surjectivity is not needed). Choose one vertex from each blow-up fibre over the RED K_k. They form a full red clique K_k in F_k. EHN/fullness on this irreducible test forces an injective red K_k in H_(i,j), whose red clique number is i. Thus k<=i. Next choose one vertex from each blow-up fibre over the BLUE C_(2k+1). Their edges form a blue odd cycle. Its image is a blue closed walk of odd length 2k+1 in H_(i,j), whose blue graph consists of C_(2j+1) and isolated red-only vertices. Such an odd closed walk has length at least the odd girth 2j+1, hence j<=k. Combining gives j<=k<=i, thus j<=i.

The **only-if** proof accommodates all arbitrary source fibre collisions and all EHN maps; it does not assume an injective or tuple-surjective image.

## Infinitely many genuine global quotient classes

The global piece setoid compares each SELECTED piece with all compatible rooted TEST charts via whether their free gluing is a member of the forbidden family. The test Q_j is legitimate; it does not have to lie in a restricted finite set.

The free amalgam of P_i and Q_j is uniquely FULL-isomorphic to H_(i,j), so the threshold shows

    Incompatible_G(P_i, Q_j)  iff  j <= i.

For i<k choose the test Q_k: it is compatible with P_k, not with P_i. Hence P_i and P_k have DIFFERENT full incompatibility profiles, and are inequivalent in the true global Myhill--Nerode quotient.

There are infinitely many such P_i. Consequently GlobalFunctionalPieceClass G 1 is infinite, violating GlobalFunctionalPieceRegular G at width 1.

## Stronger version satisfying the printed image-closure hypothesis

The original TWO-BINARY version above is a counterexample to unconditional preservation of regularity but is NOT printed-image-closed: the collapse F_i -> H_i is tuple-surjective EHN, yet H_i has no full embedded F_k (the wedge cut would contradict its vertex connectivity).

A simple enhancement gives a counterexample **even with printed image closure**. Extend the language by ONE unary relation M. Mark precisely the fibre above x in every F_i. Add one more forbidden structure F_bullet, consisting of a SINGLE marked vertex (M true), with no red or blue loops. Let

    F^M = { F_bullet } union { F_i^M : i>=3 }.

Every member is finite, connected and loopless. The unary mark changes no Gaifman edges, so the old connectivity lower bound i for F_i^M still holds, and F_bullet has no proper separating pieces. Thus F^M is regular at each positive width by the same finite-index argument.

### Exact printed tuple-surjective closure

Let f:A->B be ANY genuine EHN map from A in F^M; tuple-surjectivity is not needed. Every A has a marked vertex v whose FULL induced singleton is F_bullet. A singleton is an irreducible full source substructure. Therefore f restricted to {v} is a FULL embedding, preserving M and reflecting both false coloured loops. Hence B contains an induced FULL copy of F_bullet, which is itself in F^M.

Thus F^M satisfies the exact printed condition: every tuple-surjective EHN image of an original forbidden member contains a full forbidden substructure. In fact the conclusion holds for any EHN target map.

### The full-range saturation still has the threshold

Let H_i^M and H_(i,j)^M mark ONLY their common root x. The fibre-collapse map F_i^M -> H_i^M is still vertex-surjective EHN: irreducible source cliques cannot use two vertices from one independent fibre, and the unary mark is exactly the pullback of the target mark.

For j<=i, the blue folding walk C_(2i+1) -> C_(2j+1) can be chosen so that it reaches the marked vertex x ONLY at its start and end. Explicitly, number the target cycle vertices v_0=x,v_1,...,v_(2j). Starting from v_0, step to v_1, make (i-j) immediate two-step backtracks v_1 -> v_2 -> v_1, then traverse v_1 -> v_2 -> ... -> v_(2j) -> v_0. This is a closed surjective walk of length

    1 + 2(i-j) + 2j = 2i+1,

with no internal occurrence of v_0. Consequently the rooted map H_i^M -> H_(i,j)^M preserves and REFLECTS unary M on all irreducible singleton tests, as well as all complete two-colour clique tests. Composing with the blow-up collapse gives vertex-surjective EHN F_i^M -> H_(i,j)^M.

Conversely, if F_k^M -> H_(i,j)^M is EHN, the source full red clique K_k forces k<=i and the source blue odd cycle C_(2k+1) forces j<=k exactly as in the binary proof. F_bullet cannot surject to H_(i,j)^M because the latter has i+2j>1 vertices. Therefore

    H_(i,j)^M in Sat_EHN(F^M) iff j<=i.

Each H_i^M is saturated and has the same one-root minimal cut, now with M true on that root. The red K_i rooted pieces P_i^M and blue C_(2j+1) rooted tests Q_j^M have *identical full marked singleton roots*. Their genuine global incompatibility profiles again obey the strict threshold j<=i, producing infinitely many width-one quotient classes.

**Conclusion:** F^M is REGULAR, CONNECTED and PRINTED TUPLE-SURJECTIVE IMAGE-CLOSED, over a finite relational language with two binary colours and one unary mark; nonetheless Sat_EHN(F^M) is NOT REGULAR.

### Non-irredundancy caveat

This enhanced family is intentionally **redundant**: F_bullet fully embeds into every F_i^M. Thus its forbidden-free shadow class is precisely `Forb_EHN({F_bullet})`: a structure contains **no marked vertex whose induced singleton has both red and blue loops absent**. If ambient structures are assumed loopless, this simplifies to no M-marked vertex; however, in the unrestricted relational signature **marked vertices with a red or blue loop may be allowed** and must not be silently excluded. Neither the printed definition of a regular forbidden family nor the printed image-closure hypothesis requires F to be an antichain of minimal obstructions; this is a valid counterexample to regularity preservation under those literal premises.

It does NOT refute the printed main theorem for this trivial shadow, and it does NOT settle what happens for **irredundant** regular image-closed families. Any stronger preservation statement would need an explicit irredundancy/minimality (or other suitable) hypothesis, which should not be silently inserted into the original theorem.

## Reproducibility, formalization and scope

The accompanying Python3 standard-library regression exhausts all removals of fewer than i vertices in the examples i=3 and i=4 (379 and 18,473 deletion sets), checks rooted closed blue walks and full-on-each-clique EHN of the displayed base homomorphisms for 3<=i,j<=6, and prints the expected lower-triangular threshold matrix. This finite regression is NOT the proof of the infinite theorem.

The new native Lean file SaturationWidthOneThresholdObstruction.lean proves **conditionally** that an actual sequence of SelectedFunctionalChart F 1 with incompatibility iff j<=i yields an Infinite (GlobalFunctionalPieceClass F 1). It uses the REAL selected global chart quotient and unrestricted test charts; no model of the coloured graph family is yet defined in native Lean. A full formalization of the source blow-ups, EHN maps, lower odd-girth bounds, minimal cuts and selected-chart bridge remains open.

This result limits the saturation repair to finite/bounded families, or to extra structural hypotheses directly guaranteeing regularity of G. It does NOT refute the main 2019 conclusion through some other expansion, and does not affect the finite-family all-closed-component folded expansion already available.

## Native common-core closure bridge (additional module)

`EHNPrintedImageClosureOfCommonCore.lean` now proves (pending exact-head CI) the paper-shaped `HasTupleSurjectiveForbiddenImageClosure F` provided the family has a fixed forbidden FULL core C that embeds FULLY in every original forbidden source, and every EHN map out of C is itself fully embedded in its target. The proof is a direct composition of EHN maps followed by the embedded core; importantly it needs NO tuple-surjectivity. These premises hold for C=F_bullet, the one-marked-vertex singleton in our stronger graph family, since each source has a full marked singleton and every singleton is a full irreducible EHN test.

The theorem is intentionally general and conditional. The coloured infinite family and the unary singleton instance have not been encoded fully in native Lean; only the reusable native closure bridge plus the width-one profile-threshold implication are currently formalized as explicit theorems. Do not count the entire counterexample kernel-certified until its construction is also formalized. The complete infinite mathematical argument and executable finite checks are in this PR.
