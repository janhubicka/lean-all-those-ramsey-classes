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
