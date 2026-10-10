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

## Lean validation boundary and tasks

The printed/local (4b)-only obstruction is already Green
from PR #38. This coordinated all-n witness is **not**
Green: the uniform `C_m` family and the proof that every
weak `n`-vertex test has a K-completion still need Lean.
Finite combinatorial regressions in the upstream audit are
supporting evidence only.

Formalize these independent obligations:

1. The arbitrary-length finite gadget structures and
   embeddings of each B0 copy into C_m.
2. The maximal-clique containment lemma for every
   closed U-irreducible test, establishing (4b).
3. The gadget-label map and its fully induced behavior
   on each protected closed test, establishing (4a).
4. The exact weak `n`-vertex closure-block count and
   K-completion preserving all protected closed tests.
5. The path-transitivity contradiction for *every*
   B0-copywise completion.

Only after this test and the general higher-rank proof are
formalized should changes to arXiv or possible errata be
settled.
