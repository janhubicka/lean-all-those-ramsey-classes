# Convex order on a finite rooted amalgam of S-metric spaces

**Proof plan, 20 October 2026 — not yet a Lean theorem.**
This note is about the **metric amalgam of two original ordered spaces**.
It does not prove amalgamation of all structures in the auxiliary
functional class of the printed 2019 paper. Keep that distinction in
the printed-proof differences ledger, and do not publish an unconditional
Ramsey conclusion from these geometric components.

## Statement to formalize

Let S be a finite nonempty set of positive real distances for which
the rounded sum is well-defined and associative. Let A,U,V be finite
S-metric spaces with isometric embeddings iU:A→U and iV:A→V.
Assume the finite orders on U and V agree on A and are convex
for the equivalence relation d(x,y)≤j at each proper jump j of S.

On the **identified** finite carrier

    W = A ⊕ ((U \ iU(A)) ⊕ (V \ iV(A)))

give same-side vertices their original distances and give a left
off-base vertex x and right off-base vertex z the rounded shortest
cross distance

    δ(x,z) = min_{a∈A} [dU(x,iU a) ⊕_S dV(iV a,z)].

Then W has a linear order whose restrictions to U and V equal the
given orders and in which every proper-jump equivalence class is an
interval. The embeddings are strong in the metric and ordered
languages (but no F_j functions have yet been added).

**Completed prerequisites:** The metric and exact original-side
isometries are certified in #545/#547; exact root-only intersection
in #548. The off-base-cross jump witness is certified in #521.
PR #557 extends this witness to endpoints *on* the base as well
(and must pass its own full CI before it is cited as verified).

The empty-base case has already been verified separately in #516,
using the separated distance max(S) and concatenated order. Do not
try to minimize over an empty family.

## Proof: order the nested classes, not all private vertices at once

Write the proper jumps in increasing order j_1<...<j_k. For
convenience include level 0, whose classes are single vertices,
and a final level top=max(S), whose class is the entire nonempty
space. For each level, the classes of the relation d(x,y)≤j
are nested as j increases. These are equivalence relations by
the certified jump-threshold transitivity lemma.

For each side X∈{A,U,V}, form the finite hierarchy whose members
at level j are its j-equivalence classes, with each class lying
inside a unique class of the next larger level. At level 0 the
members are individual vertices; at the top there is one member.
Because the given order on X is convex at each jump, the children
of every class can be **linearly ordered by their vertex intervals**.
This local child order exactly recovers the order on the vertices
at the bottom.

1. **Root classes are embedded without collapsing.**
   At each jump j, the restriction of the j-equivalence relation
   from U (respectively V) to iU(A) (respectively iV(A)) is exactly
   the relation of A. Therefore distinct classes of A remain
   distinct in either side. A side class meets A in at most one
   j-class of A, and every root j-class is contained in exactly
   one j-class of each side. The child-level inclusions commute
   with these maps.

2. **The glued j-classes are known exactly.**
   A class meeting the root is the union of the U-class and
   V-class containing that root class, with their root vertices
   identified. A class disjoint from the root occurs entirely
   within one side. Indeed, a putative cross-side j-close pair
   has, by the shortest-path root-witness lemma, a root point
   within j of both endpoints. Conversely any such pair is
   j-close by metric jump transitivity. This rules out any
   additional identification of off-root classes. It also
   shows that the hierarchy of classes on W is the strong
   amalgamation of the two hierarchies over that of A.

3. **Amalgamate ordered child lists recursively.**
   Start at the top class. Suppose a common parent class is
   being treated. Its ordered children on the U and V sides
   have a common ordered sublist: precisely the children
   meeting the root, corresponding to the root's children
   at the next level. Their relative orders agree, because
   the original vertex orders agree on A. The two finite
   lists can therefore be merged, preserving each side's
   order and identifying exactly corresponding shared
   children; for instance, use the usual cut positions in
   the common sublist to merge the private children.
   Perform the same operation recursively *inside each
   shared child*. A child occurring on one side only is
   kept intact, with its original internal order. At the
   bottom the children are the original vertices and the
   recursion produces a linear order on W.

4. **Verify both required conclusions.**
   By induction over the levels, the order on the children of
   each side is unchanged and their internal orders remain
   unchanged, so the new order restricts to the original
   order on U and on V. Moreover each class at every jump
   level forms an entire consecutive range of children in
   the recursive construction; it is therefore an interval.
   By the exact class description from step 2, these are
   the actual j-equivalence classes of the S-metric on W.

This proves the *existence* of a compatible jump-convex order for
the rooted metric strong amalgam. The formalization should isolate
a reusable **finite ordered-list amalgamation** lemma and then
perform finite induction over the ordered list of jump levels.
It need not introduce a new language or assume any tie-breaker
between individual private vertices.

## Adversarial regression: why the ordinary root-cut order fails

Let S={1,3}, with proper jump 1. Take a common root {r},
the ordered left side r<x<v with d(r,x)=1 and d(r,v)=d(x,v)=3,
and the ordered right side r<y with d(r,y)=1. Both original
orders are convex at jump 1. The shortest-path amalgam has
d(x,y)=1 and d(v,y)=3. A global order obtained by placing
**all** left private points before **all** right private
points at the same root cut gives r<x<v<y, which splits the
jump-1 class {r,x,y} by v. Thus the generic key proof of
#553, even if fully certified, gives only an ORDINARY common
linear order; it cannot be cited for metric jump-convexity.

The recursion above avoids the example: the shared 1-class
{r,x,y} is kept intact before the private class {v};
inside that shared class a compatible order is r<x<y.

## Independent checks still required

- The hierarchy should use **all** proper jump thresholds of
  finite S, rather than an unproved identification with
  infinite-S maximal blocks.
- A jump-1 root class has the same identification on both
  sides only because the embeddings are *isometric*, not
  merely metric homomorphisms.
- A class disjoint from A must stay entirely on its side.
  This requires the genuine cross-root witness and must not
  be inferred from a visual diagram.
- Each shared parent requires the two child lists to agree on
  their common root-child order. Derive this from the
  original **full order embeddings** of A.
- The top level and empty spaces must be handled separately;
  do not assume every space has a nonempty list of children.
- The construction gives a metric **ordered** strong amalgam,
  not compatibility of the partial functions F_j on arbitrary
  auxiliary sources and not the corrected exact weak-subset
  completion cutoff n(B,C_0).

## Source-to-Lean comparison

The printed proof of `lem:finite4value2` does not construct
this strong metric amalgam order: it attempts an exact local
completion of an arbitrary weak structure using a bounded
nonmetric-cycle argument, then chooses orders by decreasing
jump levels. The argument above instead constructs a strong
amalgam of **already valid metric spaces** by finite nested
equivalence classes. It may supply a reusable class axiom but
does not discharge the printed proof's cycle reduction, chosen
closure points, simultaneous F_j compatibility or uniform weak
local-completion cutoff.

The original numbered manuscript text remains unchanged;
approved revisions should be small patches with separate
validation annotations and precise theorem certificates.

## Alternative direct lexicographic class-key proof (proposal, not Lean certified)

The hierarchical child-list amalgamation above can perhaps be implemented
more compactly without explicitly constructing a tree of classes. The
following **class-first key** uses the ordinary rooted order construction
#553 and a finite sequence of compatible class keys, ordered from coarser
jumps to finer jumps. Its correctness must be validated independently;
in particular one must not replace *class cuts* by the previously refuted
cuts of individual root vertices.

Fix one proper jump j. For an ordered original side X∈{A,U,V},
let L_X(x) be the **last original vertex in the j-class of x**.
This exists because X is finite. The crucial proved/under-validation
facts are:

1. L_X(x)=L_X(y) iff d_X(x,y)≤j.
2. L_X is nondecreasing along the given original convex order.
3. The relative order of two distinct j-classes is independent
   of their chosen representatives.

Item 3 is isolated in Lean PR #568; items 1–2 and the concrete
ordered class-representative carrier are in stacked PR #569.
Do not call them verified before their final full CI.

The last vertices of the j-classes in A form a finite *ordered*
set R_j. Every such class injects isometrically into U and V,
so the maps

    a∈R_j ↦ L_U(iU(a)),       a∈R_j ↦ L_V(iV(a))

are injective and strictly increasing on the j-classes, by the
representative-order lemma. Thus R_j serves as the common ordered
root **class** list at this jump, rather than the list of
individual root vertices.

For any x∈U, define its class cut

    c_U(x) = |{a∈R_j : L_U(iU(a)) < L_U(x)}|,

and analogously c_V(z). It counts root CLASSES entirely preceding
the class of x. It is constant inside each j-class and
nondecreasing along the original order. In particular,
c_U(iU(a))=c_V(iV(a)) for every a∈A, because the relative
order of root j-classes is preserved by both embeddings.

Define a class key for a side point x, with values in
a three-coordinate lexicographically ordered set. If the
j-class of x meets A, use

    K_U(x) = (c_U(x), 2, c_U(x)).

If it does not meet A, use

    K_U(x) = (c_U(x), 0, rank_U(L_U(x))).

Use the same rules on V, except replace priority 0 for private
classes by priority 1 and use rank_V. Here rank_X(t) counts
vertices of X preceding t. The private class condition is
equivalent to the absence of a root j-class witness; it is
constant on the whole class by threshold transitivity.

**Properties that must be proved:**

- K_U and K_V are constant on each original j-class and
  nondecreasing along their original vertex orders. The only
  delicate case is private versus root-touching classes in the
  same cut: a private class precedes the next shared root
  class, and its priority 0 or 1 is below the shared
  priority 2. A root-touching class followed by a private
  class necessarily has a strictly increased class cut.
  Distinct private classes in one side and one cut are ordered
  by their strictly increasing last-member ranks.
- For a∈A, K_U(iU(a))=K_V(iV(a)). Every shared j-class therefore
  receives ONE common key. A private j-class receives a
  side-specific key; no two private classes on opposite sides
  share a key. The exact class decomposition (#560/#564)
  then shows that equality of the glued keys holds **iff**
  the actual glued metric distance is ≤j.
- The resulting class key on W can be combined with ANY
  ordinary common linear order from #553, as
  `(K_j(p), ordinaryPosition(p))`. The generic label-first
  refinement PR #567 says that its order keeps j-class fibres
  convex, while preserving both old orders because K_U/K_V
  are nondecreasing there.
- For multiple proper jumps, collect the keys K_j(p) in
  **decreasing** order of j, then append the ordinary
  original-vertex tie-breaker. Because the threshold
  equivalences are nested, equality of a finer j-key
  forces equality of all preceding, coarser keys. Therefore
  every j-class remains an interval in the lexicographic
  order at every level. This is the finite-level extension
  of the two-label invariant in #567.

This provides a potentially shorter faithful formal proof of the
**ordered METRIC** strong amalgam. Compared with the child-list
construction, it needs only finite class cuts, the monotonicity
of last-member labels, and a finite lexicographic tuple lemma.
The two methods should be compared for proof length and clarity,
and only one kept in the final maintained Lean library.

Neither method supplies the printed auxiliary functional class's
strong amalgamation or the exact local-completion property. The
original `lem:finite4value2` uses bounded nonmetric cycles in
an arbitrary weak structure, and those steps must remain
explicitly marked unverified unless a source-matched proof is
completed.
