# Track D — finite seam saturation, exact proof plan (13 November 2026)

This note concerns the original 2019 **Section 3** native functional
lift and its (possibly **noninjective**) weak EHN forbidden-source
maps. The numbered manuscript is frozen. No collaborator-deleted
validation marker is restored here.

## Setup

Take a finite connected **genuinely forbidden** old-language native
functional structure `F0` and a native EHN map

`f : F0 -> D = A ⊕_X B`

into a **genuine FULL** functional free amalgam of forbidden-free
sides. Let `R = f^{-1}(X)` be the **actual original source**
preimage of the complete common FULL root. The verified weak-map
preimage lemma shows that `R` is function-closed. The true full
free-amalgam source partition supplies an original left-exclusive
vertex `x` and a right-exclusive vertex `y`. The Gaifman
localization theorem shows that **every** path in `F0` from
`x` to `y` meets `R`.

Let `H0` be **any** native function-closed original source subset
with `H0 ⊆ R`; in the seam-only positive target-incidence defect,
take the actual native hull of the original source input generators.
No image quotient is substituted for either `F0` or `H0`.

## Finitary saturation lemma — English proof

There exist `k ≤ |R| - |H0|` and genuine closed source sets

`H0 ⊊ H1 ⊊ ... ⊊ Hk ⊆ R`

such that, for each `i < k`:

1. The original source contains a Gaifman path from `x` to `y`
   avoiding `Hi`.
2. Along a path avoiding `Hi`, a **first** left-exclusive-to-seam
   Gaifman attachment edge `a_i -- z_i` occurs, with the actual
   seam vertex `z_i ∈ R \ Hi` and an original path from `x`
   to `a_i` avoiding `Hi`.
3. Set `H(i+1) = cl_F0(Hi ∪ {z_i})`. Since `R` is function-closed,
   `H(i+1) ⊆ R`, while `z_i ∉ Hi` forces strict growth.

The final `Hk` **separates** `x` and `y` in the original
Gaifman graph (they lie in distinct connected components of
`F0 \ Hk`).

**Proof.** At a closed stage `Hi ⊆ R`, check whether there is a path
from `x` to `y` avoiding `Hi`. If none exists, stop. Otherwise
choose such a path. It cannot go from the left-exclusive region to
the right-exclusive region while avoiding the common-root preimage
`R`. Before its first root-preimage vertex all vertices are
left-exclusive, since native weak maps preserve positive source
Gaifman adjacency up to collapse and the genuine full amalgam has
no positive cross-exclusive tuple. Thus it contains a positive
old-language/function-graph source edge `a_i -- z_i`, with `a_i`
left-exclusive and `z_i ∈ R \ Hi`. The target root is full and
function-closed; its preimage `R` is therefore closed, so taking
the entire **native** function closure stays in `R`.
The new source hull contains `z_i` but `Hi` does not:
`|H(i+1)| ≥ |Hi| + 1`. Finiteness bounds the number of steps by
`|R| - |H0|`. A path avoiding `R` cannot exist, so the process
must stop at a separating closed source subset.

No assumption about function arity, image-root injectivity or
forbidden-source test coverage was used for this finite saturation
argument. It retains every native function output fibre.

## Final geometric selection

Since `Hk` is an **actual closed separator** in the finite
original source, the verified finite minimal-closed-separator
selection produces an inclusion-minimal closed `C ⊆ Hk` separating
`x,y`. Enumerating **every** vertex of `C` by an injective
ordered original source tuple gives an authentic
`GeometricFunctionalPieceData`, not an arbitrary rooted pattern.
Connectedness of `F0` forces positive width. The resulting
rooted pattern belongs to the genuine forbidden-piece family.

This endpoint says only **the selected source root lies in
the terminal hull**; it does not say that the original input hull,
the chosen seam attachment vertices, or the starting target-only
incidence are retained in that final minimal closed root.

## Lean coverage and explicit remaining gap

The following endpoints are separate, and must not be collectively
reported as kernel-certified until their current exact-head checks
pass and are merged:

- [#1111](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1111):
  a closed separator with two exterior components gives a positive
  genuine forbidden geometric piece;
- [#1116](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1116):
  either the native input hull already separates, or a path avoiding
  the hull reaches a fresh common-seam source vertex;
- [#1126](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1126):
  the first **left-exclusive–seam source attachment edge**;
- [#1125](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1125):
  strict native closure growth and a general finite witnessed
  termination theorem, proved by strong induction on
  `|Root| - |S|`.

A unified Lean instantiation of the general finite saturation
theorem with the **first seam attachment edge** as its certified
progress predicate, plus selection of the final genuine forbidden
piece, remains an explicit integration task. This English proof
does not certify that missing Lean composition.

**Critical remaining mathematics:** The original global canonical
lift attaches a piece-class relation only to **injective ordered
target root images**. The selected piece above may have colliding
images, even when its original source roots are distinct and even
when the two side witnesses have a complete common canonical lift.
Saturation and minimal-cut selection do **not** prove target-root
injectivity, compatibility of a replacement's **entire old
functional root and incompatibility profile**, or strict descent
of the **original source exclusive support count**. Those missing
facts are the genuine collision-tolerant original Section 3
Claim 1/Claim 2 flip obstruction.

In particular, it is unsound to call this a proof of unrestricted
strong AP or of the printed Ramsey theorem, or to repackage a
forbidden-free input-generated source hull as a forbidden
geometric subpiece.
