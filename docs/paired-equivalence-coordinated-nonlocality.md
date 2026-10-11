# Why paired equivalences are not locally finite under the coordinated repair

**Mathematical proof note, not yet a Lean certificate.** This follows the
all-cutoff construction in
[the upstream audit](https://github.com/janhubicka/partite-construction/blob/audit/2019-singleton-vacuity-paired-equivalences-20261009/docs/paired-equivalence-local-finiteness-correction.md).
The paired equivalence and matching class **does** satisfy the
**(4b)-only** repair: this is already Lean-verified by
`finitePairedClass_corrected_local_cutoff` at `n = |C0| + 1`.
The construction here uses a *different*, coordinated convention:
`IsClosedUHomomorphismEmbedding` in (4a) and (4c),
and `ClosedUIrreduciblesIn` in (4b).

## Fixed target B and control C0

Work in the original binary relational language `<, E, M`.
`K` contains finite strictly ordered sets where `M` is a
symmetric irreflexive perfect matching, `E` is an equivalence
relation, and `M ⊆ E`. The closure rule uses the unique `M`
output of each reflexive `E`-root. Equivalence classes need
**not** be convex in the vertex order.

Fix a six-vertex `B0`: three consecutive matching blocks,
with `E`-class pattern **X,X,Y**.
Fix a ten-vertex control `C0`: five ordered matching blocks
**A < B < T < C < D**. The only positive cross-block `E`
relations are `AB`, `BC`, and `AT`. Its E relation is not
transitive (`A E B E C` but `¬A E C`), as is permitted in
the ambient Ramsey class R.

## Witness C_m for an arbitrary cutoff n

Given any n, choose odd `m ≥ 5` with `m > n`. Introduce
backbone matching blocks `b_0,…,b_(m−1)` with labels
`A,B,A,B,…,B,C`. For each consecutive backbone edge,
adjoin one private matching block `t_i` labelled `D`.
Also adjoin a private block `t_*` labelled `T`.

Install induced copies of `B0` on each triple
`{b_i,b_(i+1),t_i}`, ordering its blocks by their A/B/C/D
labels, and on the closing triple `{b_0,t_*,b_(m−1)}`,
whose labels are A,T,C. Relations not belonging to an
installed copy are absent. Internal matching-pair relations
are fixed consistently on every overlap.

The block-interaction graph is a long chordless cycle, with
a private triangle gadget on each edge. Its cliques involving
three blocks are exactly the installed B0 gadgets.

## Verify the three antecedents for EVERY n

**(4a)** The original block-label map `C_m → C0` is a
positive homomorphism. Every **closed U-irreducible** test
must have its support in one block clique and therefore lies
in an installed B0 gadget, where the label map is an induced
embedding. Thus it is a valid completion **only for the
coordinated closed-test map notion**. It need not be a
literal 2019 U-homomorphism-embedding.

**(4b)** Every closed U-irreducible substructure is an
induced substructure of one valid B0 gadget. It belongs to
K by closed hereditariness.

**(4c)** Take any exact induced weak vertex subset `S`
with `|S| ≤ n`, possibly omitting mates. Its U-closure
adjoins the missing mates and meets at most `n` backbone
blocks. Since `m > n`, at least one backbone block is
missing, so the represented positive E-path cannot link
the two endpoints. Complete E by the equivalence closure
of positive E-edges; this does not contradict the absent
E-relations in the represented B0 gadgets. Extend the
partial order using the C0 label order with tie-breaking,
retain M, and take the same finite K target for the weak
source S by restriction. The restriction remains a
closed-test U-homomorphism-embedding.

## Why there is no copywise B0-completion

Any map respecting every installed B0-copy must preserve
positive E on each consecutive backbone edge. Since the
target E is transitive, this forces the first and last
backbone blocks to be equivalent. The closing B0-copy
requires those same endpoints to be inequivalent. Its
embedding must reflect that negative E relation.
This contradiction rules out **every** K-valued B0-copywise
completion of `C_m`. Hence the corrected local implication
fails for the same fixed `B0, C0` at **every possible
cutoff n**.


## Explicit gap-count completion for every weak test (mathematical proof)

For arbitrary cutoff $k=n$, let $m=2k+5$ and take the *original*
weak vertex set $S\subseteq V(C_k)$, with $|S|\leq k$. No assumption
that S is U-closed is made. A touched matching block counts as present
even if S contains only one of its two vertices. Let
$T=\{b:\exists v\in S,\ v.\mathrm{block}=b\}$; in particular
$|T|\leq k$.

The already Lean-certified internal-gap lemma (#76) gives an
**internal** index $1\leq h<m-1$ whose matching block has no
vertex in S: adding one root at each endpoint creates a set of at
most $k+2<m$ vertices, so a missing block cannot be an endpoint.

Define the gap count $g_T(i)=|\{j<i:j\notin T\}|$ for the
backbone indices. On the **entire original matching-pair carrier**
$V(C_k)$ (not merely on the tested vertices) assign each block
an equivalence-class tag:

* backbone $b_i\mapsto(0,g_T(i))$;
* closing private block $t_*\mapsto(0,0)$;
* path-private block $t_i\mapsto(1,m+i)$.

Put $E_D(x,y)$ iff these tags agree. Retain the original perfect
matching M. Order the vertices lexicographically by
$(\mathrm{controlVertex}(x),\mathrm{blockIndex}(x))$: the first
coordinate records the 10-vertex C0 label *and* matching bit,
and the second breaks ties when different blocks have the same
control image. Together these define the explicit structure
`cycleWeakCandidate k S`, a **finite member of K** for every S.
This membership is Lean-checked in merged PR #81.

For any pair x,y *in S* whose blocks occur in a common installed
gadget, compare the old and new binary relations. The matching
tuples agree everywhere. The named order agrees since different
blocks of the same gadget have distinct C0 labels and within a
block the control value already distinguishes the two bits; the
block-index tie breaker is never used on an unequal pair in
one gadget. These facts are Lean-checked in PRs #74 and #83.

For E, all possibilities come from the three-block gadgets:

* Each block is internally E-complete.
* The two backbone blocks of any path gadget are positively
  E-related. If both appear in S, its *first* backbone index i
  belongs to T, whence $g_T(i+1)=g_T(i)$; they retain equal tags.
* Its path-private D block has a tag with first coordinate 1,
  hence is E-inequivalent to either backbone block.
* In the closing gadget, b0 and t_* both carry tag (0,0),
  whereas the final backbone block carries
  $(0,g_T(m-1))$. Since the internal gap h is absent,
  $g_T(m-1)>g_T(0)=0$; hence this last block is
  E-inequivalent to both b0 and t_*.

The gap-count recurrence and internal-gap theorem are Green
(#75/#76); the closing-endpoint and path-private E comparisons
are Green (#84/#85), with full all-pairs composition in #89/#91
still awaiting Lean validation. Thus **all binary tuples,
positive and negative, agree on every gadget-supported pair
of vertices of the exact S**. Unrelated pairs have no positive
source tuples, so the canonical inclusion $C_k|S\to D(k,S)$
is a positive homomorphism even though D may add relations on
unrelated pairs.

Every embedded *U-closed U-irreducible* test inside $C_k|S$
has pairwise gadget-related matching blocks by the checked
closed-cover argument (#66), and these blocks lie in one common
gadget by #73. Consequently its image into D is a **full induced
embedding**: precisely the amended U-homomorphism-embedding
requirement. Because S was never enlarged or assumed closed,
this proves (4c) for the *original exact weak test* once the
final related-pair reflection and its formal Lean packaging
(#86/#91/#92) are certified.

## The actual global obstruction and all-cutoff package

In each consecutive path gadget, two backbone matching blocks
form the positive E pair inside an **induced B0 copy**. The closing
gadget has another induced B0 copy with the first and last
backbone blocks E-inequivalent. Induced B0 gadget existence
and the two closed-test antecedents (4a) and (4b) are now
Lean-checked for **every k** in #82.

Any single K-target map respecting all those B0-copies must
preserve every backbone-positive E edge, and therefore must
identify its first and last blocks in the target's transitive E.
The closing induced B0 copy requires them E-inequivalent.
This contradiction is the previously verified abstract path
lemma; its application to the concrete Ck is being checked
in PR #90.

Once the universally quantified (4c) and actual copywise
obstruction are Lean-green, PR #93 will produce, for the
SAME fixed B0 and C0, a bad witness at **every cutoff k**.
It then follows that finite paired equivalences are *not*
locally finite under the COORDINATED revised Definition 2.17.
This is NOT a proof of the repaired positive Theorem 2.18.

## Lean validation boundary (11 October 2026)

**GREEN / theorem-level:** literal printed and (4b)-only
Theorem 2.18 refutations (#56); finite K strong amalgamation
(#49); actual closed relational Ck and positive projection
(#59/#60); finite matching-block interaction graph (#73);
all induced B0 gadget embeddings and uniform coordinated
(4a),(4b) for actual Ck (#82); a finite K target D(k,S)
for every exact weak S (#81); the internal missing-block
and component arithmetic (#75/#76/#83/#84/#85).
The latter are genuine Lean proofs, not finite searches.

**PENDING:** the full E reflection on all supported pairs in
an arbitrary exact weak S (#87–#91), the implication to
HasClosedUKCompletion for every S.card<=k (#86/#92), the
actual positive-path / negative-closing B0 obstruction (#90),
and the final all-cutoff nonlocal-finiteness theorem (#93).
An independent exhaustive regression for k=0,…,4 with
309,136 exact weak sets is in #94. It does not replace
the universal formal proof.

**Open beyond the counterexample:** a repaired general
multiamalgamation Ramsey theorem and higher-rank picture
construction. Keep the literal 2019 mathematical prose
frozen pending theorem-level validation and author review.
