# Strong amalgamation of finite ordered paired equivalences

## Statement

Let \(\mathcal K\) consist of finite structures \((V,<,E,M)\) where
\(<\) is a strict linear order, \(E\) is an equivalence relation,
\(M\) is a symmetric irreflexive perfect matching, and \(M\subseteq E\).
For any full embeddings \(s_L:D\hookrightarrow L\) and
\(s_R:D\hookrightarrow R\) with \(D,L,R\in\mathcal K\),
there exists a finite strong amalgam \(P\in\mathcal K\) over \(D\).

This is a **mathematical proof**, not yet a Lean declaration. It gives
the complete construction targeted by the outstanding
`HasFiniteStrongAmalgamation finitePairedClass` obligation.

## Step 1: strong vertex pushout, matching

Take the strong vertex pushout
\(P_0=L\sqcup_D R\): identify precisely
\(s_L(d)\sim s_R(d)\), and no other vertices. The concrete
`RelStructure.FreeAmalgam` construction in
`partite-construction` already formalizes this vertex set and its
two full relational side embeddings for the *free* structure.

Because \(D\) itself has a perfect matching and each embedding
reflects \(M\), the two side matchings agree on every identified
vertex. Their union is therefore again a symmetric irreflexive
perfect matching \(M_P\) on \(P_0\).
Lean has proved that the initial free amalgam is
\(\mathcal U\)-closed for the actual unary matching closure
(`freeAmalgam_matching_isUClosed`). The explicit `freeAmalgam_mate_total` theorem is now
Lean-verified in main. The free relational amalgam's M relation
remains unchanged by the later E and order completions.

## Step 2: equivalence classes without unwanted identifications

Write \(Q_D=D/E_D\), \(Q_L=L/E_L\), and \(Q_R=R/E_R\)
for the equivalence-class sets. Each full embedding induces an
**injective** map of quotient sets
\(\bar s_L:Q_D\hookrightarrow Q_L\) and
\(\bar s_R:Q_D\hookrightarrow Q_R\).
Indeed, equality of images means \(s_L(d)E_Ls_L(d')\),
equivalent by reflection to \(dE_Dd'\), and similarly on the right.

Form the disjoint union of class labels
\[
Q = Q_D\;\sqcup\;
    (Q_L\setminus \bar s_L(Q_D))\;\sqcup\;
    (Q_R\setminus \bar s_R(Q_D)).
\]
Associate to a left vertex \(x\in L\) its \(E_L\)-class
if that class misses \(s_L(D)\), tagged as a left-only class.
Otherwise it has a **unique** class \([d]\in Q_D\)
with \([x]=\bar s_L([d])\), and assign the common label
\([d]\). Do the symmetric construction on the right.

This is well-defined: if the \(E_L\)-class of \(x\) meets
the image of two vertices \(d,d'\in D\), then
\(s_L(d)E_Ls_L(d')\), hence \(dE_Dd'\).
It also agrees on each common vertex:
\(s_L(d)\) and \(s_R(d)\) get the same common label \([d]\).

Thus we obtain \(q:P_0\to Q\).
Define \(E_P(x,y)\) exactly when \(q(x)=q(y)\).
This is an equivalence relation by definition. Its restriction to
\(L\) is exactly \(E_L\), since the label map on
\(Q_L\) is injective; likewise on \(R\).
The root class compatibility lemmas
`equivalence_embedding_iff`,
`root_class_unique_of_two_contacts`, and
`equivalence_agrees_on_overlap` isolate the reflection and
uniqueness properties required for this formalization.

Every matching edge \(M_P(x,y)\) came from one side.
On that side \(M\subseteq E\), and its two endpoints therefore
have the same label. Hence \(M_P\subseteq E_P\).

**Important:** taking the transitive equivalence closure of the
union of the two side relations gives the same relation, but the
quotient-label construction makes transitivity and preservation of
both induced side embeddings transparent and avoids an induction
over arbitrary zigzags.

## Step 3: extend both linear orders

Identify \(D\) as its common image in \(P_0\), and list its
vertices in increasing common order \(d_1<\cdots<d_k\).
This determines \(k+1\) open intervals (before \(d_1\),
between consecutive root vertices, and after \(d_k\)).
Every vertex outside \(D\) belongs to exactly one interval,
as calculated in its own side, since both side embeddings
preserve and reflect the order on \(D\).

In each interval, concatenate **all left-only vertices in their
original left order**, followed by **all right-only vertices in
their original right order**. Insert the common \(d_i\)'s between
these interval lists. This defines a strict linear order on
\(P_0\), extends both original orders, and creates no new
identifications. For \(k=0\) it simply lists all left vertices
followed by all right vertices. Finiteness is immediate.

## Conclusion and remaining Lean obligations

Interpret \(P=(P_0,<_{P},E_P,M_P)\).
The construction is finite and belongs to \(\mathcal K\);
both side embeddings are full (they reflect absent \(E\),
\(M\), and order tuples), agree on \(D\), and their ranges
intersect **exactly** on \(D\).
This proves strong amalgamation mathematically.

The exact Lean work outstanding is:

1. Construct the quotient-label type \(Q\) and label maps using the
   two induced injections \(Q_D\hookrightarrow Q_L,Q_R\);
   prove root agreement and side injectivity.
2. Use label equality to construct \(E_P\) and prove each side
   embedding reflects it. The three overlap lemmas are a reusable
   starting point.
3. Construct the finite linear order by the \(k+1\) root intervals
   and prove both side embeddings strictly monotone and induced
   for order tuples.
4. Combine these with the already-verified free vertex carrier and
   matching closure to prove
   `HasFiniteStrongAmalgamation finitePairedClass`.
5. Apply the class-level literal-counterexample assembly theorem
   (currently a separate PR) to close the only missing original
   multiamalgamation hypothesis.

**Do not change the manuscript while this Lean formalization remains
incomplete.** This note is a source for review and a proof guide,
not a completed machine-verification certificate.

## Lean implementation checkpoint — 10 October 2026

CI-verified and merged:

- `FreeAmalgam.isFreeAmalgam` (upstream) supplies the exact strong vertex
  pushout and induced side embeddings.
- `freeAmalgam_matching_isUClosed` and `freeAmalgam_mate_total`
  establish the original M-closure and the unique mate of every vertex.
- `equivalence_embedding_iff`, `root_class_unique_of_two_contacts`,
  and `equivalence_agrees_on_overlap` prove E-class compatibility.
- `sideClassTag_eq_iff` and `amalgamTag_agree_on_root` identify the exact
  quotient classes over the root. `leftAmalgamTag_eq_iff` and
  `rightAmalgamTag_eq_iff` protect full E-reflection on both sides.
- `rootCut_mono` and `rootCut_agree_on_root` support the root-interval
  linear-order construction.

Open, CI-PENDING proof stages (do NOT treat these as verified until
their own completed workflow and axiom audit are checked):

- [PR #39](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/39):
  glues compatible class labels over the actual free vertex pushout.
- [PR #40](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/40):
  stacked on #39; defines E by global label equality, checks full
  E-reflection and M-contained-in-E.
- [PR #41](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/41):
  strict rank of side vertices and root-cut separation.
- [PR #43](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/43):
  stacked on #41; root-compatible strict lexicographic keys for the sides.
- [PR #44](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/44):
  stacked on #39; generic finite order extension from compatible
  monotone keys using an injective lexicographic tie-breaker.

After these modules have passed CI, combine the side keys from #43
with the generic order-lifting theorem from #44 to obtain the common
linear order. Define the target ternary structure on the concrete
free carrier using this order, global E-label equality and the original
free M relation. Prove its pairedClass membership and the full induced
left/right embeddings, then conclude
`HasFiniteStrongAmalgamation finitePairedClass`.

**Important mathematical update:** the published 2019 theorem and the
proposed (4b)-only repair both have paired-class counterexamples.
The (4b)-only corrected local completion condition was proved in Lean
in PR #38 (CI 38083046493), with cutoff `Nat.card C0 + 1` for every
B in K. The only remaining machine-checking obligation for these
class-level contradictions is the finite strong amalgamation theorem
above. This does not validate any alternative repair of Theorem 2.18.
