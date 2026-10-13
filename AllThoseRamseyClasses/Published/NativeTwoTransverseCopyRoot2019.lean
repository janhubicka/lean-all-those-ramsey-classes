import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide
import AllThoseRamseyClasses.Published.NativeOldCopyWeakPiece2019
import PartiteConstruction.Ramsey.ClosureTransverseLineRootLetters

/-!
# Genuine two-copy transverse native Hales--Jewett roots

For the corrected 2019 Lemma 2.30, the native Hales--Jewett
attachment maps must not be replaced by a fictitious globally
injective projection or by ordinary part-label compatibility.

A special but useful TRUE native geometry is available for TWO
attached Old-copy indices i≠j with disjoint parameter-coordinate
sets. If two old vertices x,y have the SAME actual attachment
image, both necessarily lie in the attaching support. Equality of
their line maps then forces them to factor through TWO genuine
A-letters e,d (actual full induced embeddings) with ONE common
abstract root part q. This applies simultaneously to an arbitrary
family of common-root vertices.

Consequently, if a maximal-U-rank exact weak source is ALREADY
known to be a genuine relational free amalgam of TWO pieces
whose ordinary native images lie respectively in those two
attached copies, the existing checked two-ordinary-side map
gluing theorem completes that exact source. Properness and
the two <=j source-side cardinal bounds remain explicit.

This does not establish a free two-copy cover for an arbitrary
native source: pure core relations may contain vertices from
different copy images. Nor does it handle three or more active
copies with pairwise intersecting but globally noncommon
parameter sets. A global native j→j+1 Picture constructor and
corrected Theorem 2.18 are NOT claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- Two DIFFERENT genuinely attached old copies have intersection
only on the common core/support. Under pairwise transverse HJ lines,
the inverse old vertices over ANY common-root family factor
through two actual full induced A-letter embeddings, with ONE q.

Crucially this gives VERTEX identities, not mere equality of
outer part labels. There is no closure assumption here. -/
theorem native2019_two_transverse_copies_actual_A_root
    {P Q V I H : Type v} {N : ℕ}
    (Old : System L P V) (alpha : Q ↪ P)
    (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (i j : I) (hij : i ≠ j)
    (hTransverse : ∀ k : Fin N,
      (lines i).symbol k = .parameter →
      (lines j).symbol k ≠ .parameter)
    (x y : H → V)
    (hSame : ∀ r : H,
      copyMap Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) i (x r) =
      copyMap Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) j (y r)) :
    ∃ (aL aR : Embedding A Old.toRelStructure)
      (q : H → Q),
      (∀ r : H, x r = aL (q r)) ∧
      (∀ r : H, y r = aR (q r)) := by
  classical
  let S := Old.support alpha
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  have hxS (r : H) : x r ∈ S := by
    by_contra hn
    have hout : OutsideAt (W := NonInduced.Vertex
        (Old.restrict alpha) N) (I := I) S i
        (copyMap Old.toRelStructure S Core maps i (x r)) :=
      ⟨⟨x r, hn⟩, (copyMap_not_mem i (x r) hn).symm⟩
    rw [hSame r] at hout
    exact (copyMap_not_outside_of_ne
      (B := Old.toRelStructure) (S := S)
      (D := Core) (f := maps) (i := i)
      j hij (y r)) hout
  have hyS (r : H) : y r ∈ S := by
    by_contra hn
    have hout : OutsideAt (W := NonInduced.Vertex
        (Old.restrict alpha) N) (I := I) S j
        (copyMap Old.toRelStructure S Core maps j (y r)) :=
      ⟨⟨y r, hn⟩, (copyMap_not_mem j (y r) hn).symm⟩
    rw [← hSame r] at hout
    exact (copyMap_not_outside_of_ne
      (B := Old.toRelStructure) (S := S)
      (D := Core) (f := maps) (i := j)
      i hij.symm (x r)) hout
  let xs : H → S := fun r => ⟨x r, hxS r⟩
  let ys : H → S := fun r => ⟨y r, hyS r⟩
  have hLine (r : H) :
      NonInduced.lineMap (lines i) (xs r) =
        NonInduced.lineMap (lines j) (ys r) := by
    have h := hSame r
    rw [copyMap_mem i (x r) (hxS r),
        copyMap_mem j (y r) (hyS r)] at h
    change Sum.inl (NonInduced.lineMap (lines i) (xs r)) =
      Sum.inl (NonInduced.lineMap (lines j) (ys r)) at h
    exact Sum.inl.inj h
  obtain ⟨e, d, q, he, hd⟩ :=
    transverse_lines_compatible_root_parts
      A (Old.restrict alpha) (lines i) (lines j)
      hTransverse xs ys hLine
  let inc : Embedding (Old.restrict alpha).toRelStructure
      Old.toRelStructure :=
    inclusion Old.toRelStructure S
  let aL : Embedding A Old.toRelStructure := inc.comp e.toEmbedding
  let aR : Embedding A Old.toRelStructure := inc.comp d.toEmbedding
  refine ⟨aL, aR, q, ?_, ?_⟩
  · intro r
    exact congrArg Subtype.val (he r)
  · intro r
    exact congrArg Subtype.val (hd r)

/-- A restricted but GENUINE transverse higher-rank completion
case. Assume the exact maximal-rank source has an ACTUAL free
amalgam decomposition and the two whole induced sides map into
two different attached old-copy ranges whose HJ parameter sets
are disjoint. Then TWO ordinary old-side maps exist, and their
entire common root automatically has a SINGLE vertex-exact
A-letter boundary, constructed above.

Previous CLOSED rank-j Old completions then complete the original
exact source. No completion is assumed for the nonclosed sides or
root, and no original source vertices are added or discarded. -/
theorem native2019_two_transverse_copy_free_source_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V I H E F C : Type v} {N : ℕ}
    [Fintype C] [Fintype E] [Fintype F]
    [Finite V] [Finite Q]
    {Root : RelStructure L H}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (Old : System L P V) (alpha : Q ↪ P)
    (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (i j : I) (hij : i ≠ j)
    (hTransverse : ∀ k : Fin N,
      (lines i).symbol k = .parameter →
      (lines j).symbol k ≠ .parameter)
    (p : C → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Whole.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (hLeftRange : ∀ x : E, ∃ y : V,
      p (iL x) = copyMap Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) i y)
    (hRightRange : ∀ x : F, ∃ y : V,
      p (iR x) = copyMap Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) j y)
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    (hDClosed : IsUClosed rules Old.toRelStructure)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (rank : ℕ)
    (hSmallL : Fintype.card E ≤ rank)
    (hSmallR : Fintype.card F ≤ rank)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ rank →
        HasInducedClosedUKCompletion K rules
          (Old.toRelStructure.induce T)) :
    HasInducedClosedUKCompletion K rules Whole := by
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let Attachment := attach Old.toRelStructure (Old.support alpha)
    Core maps
  have hpL : Left.IsHomomorphismEmbedding Attachment (p ∘ iL) :=
    hp.comp iL.isHomomorphismEmbedding
  have hpR : Right.IsHomomorphismEmbedding Attachment (p ∘ iR) :=
    hp.comp iR.isHomomorphismEmbedding
  obtain ⟨fL, hfL, hCopyL⟩ :=
    ordinaryHE_factor_through_embedded_copy_2019
      hpL (copyEmbedding Old.toRelStructure (Old.support alpha)
        Core maps i) hLeftRange
  obtain ⟨fR, hfR, hCopyR⟩ :=
    ordinaryHE_factor_through_embedded_copy_2019
      hpR (copyEmbedding Old.toRelStructure (Old.support alpha)
        Core maps j) hRightRange
  have hSame (r : H) :
      copyMap Old.toRelStructure (Old.support alpha) Core
        maps i (fL (sL r)) =
      copyMap Old.toRelStructure (Old.support alpha) Core
        maps j (fR (sR r)) := by
    calc
      copyMap Old.toRelStructure (Old.support alpha) Core
        maps i (fL (sL r)) = p (iL (sL r)) :=
          (hCopyL (sL r)).symm
      _ = p (iR (sR r)) := by
          apply congrArg p
          exact (hFree.overlap (sL r) (sR r)).mpr ⟨r, rfl, rfl⟩
      _ = copyMap Old.toRelStructure (Old.support alpha)
        Core maps j (fR (sR r)) := hCopyR (sR r)
  obtain ⟨aL, aR, q, hRootL, hRootR⟩ :=
    native2019_two_transverse_copies_actual_A_root
      Old alpha A hRestricted lines i j hij hTransverse
      (fL ∘ sL) (fR ∘ sR) hSame
  exact inducedClosed2019_maximal_weak_two_ordinary_side_maps_via_A
    rules hStrong hHer hKIrr hFree hMax hDClosed
    hAK hAClosed q fL fR hfL hfR aL aR
    hRootL hRootR rank hSmallL hSmallR hOldRank

end AllThoseRamseyClasses.Published
