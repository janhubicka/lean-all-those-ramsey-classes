import AllThoseRamseyClasses.Lifts.Claim2NoEscapeFullAmalgamTransfer
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftPieceFlip
import AllThoseRamseyClasses.Lifts.GlobalFlipContextOutsideSupport
import AllThoseRamseyClasses.Lifts.FullComplementClosedOuterRoot
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Track C: an actual canonical B→A flip within ANY closed no-escape context

The original Section 3 Claim 2 repeatedly flips B-only rooted
subpieces inside a changing outer context. The old proofs required
the whole context to be a geometrically minimal closed separator,
which is not known to survive a literal replacement.

The weaker source invariant is a function-closed no-escape set
K containing the FULL selected inner source geometric piece d.
For the OLD full native source decomposition
  Forbidden = d +_U E
write SR = {b in E | oldComplement(b) belongs to K}.
Then automatically:
* SR is function-closed and contains the whole gluing root U;
* the old source context K is EXACTLY the union of the whole
  embedded inner piece and the retained E|SR;
* the source's no-escape property holds in that diagram.

Perform ONE original-global canonical right-to-left flip on the
actual geometric INNER piece d. The chosen new forbidden source
  New = Q +_U E
has an actual EHN map to the same target, equal to the old map
on the COMPLETE native complement E. If d has positive root
width, injective target-root coordinates and a B-only selected
component with a B-exclusive source vertex, the entire B-support
of New is strictly smaller.

The real full-source outside-support bijection then yields:
* strict decrease of B-exclusive SOURCE cardinality INSIDE KNew;
* exact conservation of A-exclusive SOURCE cardinality OUTSIDE KNew;
* closedness of KNew;
* no-escape of KNew relative to the NEW full root preimage SNew.

This is a genuine one-step theorem with a SINGLE actual F-member,
not a splice of incompatible existentials. It needs NO geometric
minimal-cut data for the ambient old K and NO intermediate A-
minimality. Its still-explicit premise is the existence of the
genuine flippable inner piece d. A further rooted all-test profile
transport must be composed via generic contextual reassociation;
the terminal original canonical relation still needs an eligible
selected genuine geometric outer piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One genuine B-to-A canonical source flip works inside an
arbitrary CLOSED NO-ESCAPE context containing the original
selected inner geometric piece. The new context is again
closed/no-escape, its local B source rank strictly decreases,
and its exterior A source count is unchanged.

Neither outer context is required to be a minimal-separator
geometric piece. The given d IS genuine source-geometric
selected data, as required by the original global lift.
The weak source-to-target map need only be injective on the
chosen ordered INNER root, not on the entire seam. -/
theorem claim2_actualRightFlip_in_closedNoEscapeContext
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {m : ℕ} (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (K : Set V) (hKclosed : Forbidden.IsClosed K)
    (hInnerInside : geometricPieceVertices Forbidden d ⊆ K)
    (Target : Structure L UT)
    (f : V → UT) (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hKnoEscape : FunctionalContextNoEscapeOutsideSeam
      Forbidden (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) K)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hRootInjective : Function.Injective
      (fun i : Fin m => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    let E := geometricGlobalComplementChart Forbidden d
    let SR : Set E.Carrier :=
      (functionalComponentComplementEmbedding Forbidden
        (Set.range d.roots) d.minimal.1 d.left) ⁻¹' K
    ∃ (W : Type) (New : Structure L W), F New ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding E.str New),
        Structure.IsFreeAmalgam Q.rootEmbedding E.rootEmbedding iQ iE ∧
        ∃ (flip : W → UT),
          New.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ b : E.Carrier, flip (iE b) = f b.1) ∧
          New.IsClosed
            (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) ∧
          FunctionalContextNoEscapeOutsideSeam New
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
            (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) ∧
          Nat.card {w : W //
            w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) ∧
            flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            v ∈ K ∧ f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
          Nat.card {w : W //
            w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) ∧
            flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
          Nat.card {v : V //
            v ∉ K ∧ f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  let E := geometricGlobalComplementChart Forbidden d
  let Inner := (geometricGlobalFunctionalChart Forbidden d).ext
  let iOldInner : Structure.Embedding Inner.str Forbidden :=
    functionalComponentEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  let iOldE : Structure.Embedding E.str Forbidden :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  let SR : Set E.Carrier := iOldE ⁻¹' K
  have hOldFree :
      Structure.IsFreeAmalgam Inner.rootEmbedding
        E.rootEmbedding iOldInner iOldE :=
    geometricGlobalSource_freeDiagram Forbidden d
  have hSRclosed : E.str.IsClosed SR :=
    functionalEmbedding_preimage_closed
      E.str Forbidden iOldE K hKclosed
  have hRootSR : ∀ i : Fin m, E.rootEmbedding i ∈ SR := by
    intro i
    change d.roots i ∈ K
    exact hInnerInside (Or.inl ⟨i, rfl⟩)
  have hOldCarrier :
      iOldInner '' (Set.univ : Set Inner.Carrier) ∪
        iOldE '' SR = K := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with hzInner | hzE
      · obtain ⟨a, _ha, rfl⟩ := hzInner
        exact hInnerInside a.2
      · obtain ⟨b, hbSR, rfl⟩ := hzE
        exact hbSR
    · intro z hz
      rcases hOldFree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact Or.inl ⟨a, Set.mem_univ _, ha.symm⟩
      · exact Or.inr ⟨b, (by simpa only [SR] using
          (show iOldE b ∈ K from hb ▸ hz)), hb.symm⟩
  obtain ⟨Q, _hEq, g, _hg,
    W, New, hNew, iQ, iE, hNewFree,
    flip, hFlip, hQImage, hEImage⟩ :=
    geometricGlobalCommonFullLiftFlip_rightToLeft
      F Forbidden hFinite hForbidden
      d hm Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hRoots hNoLeft hRootInjective
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite W := hFiniteF New hNew
  letI : Fintype W := Fintype.ofFinite W
  letI : Finite E.Carrier :=
    Finite.of_injective (fun b : E.Carrier => b.1)
      (by intro a b hab; exact Subtype.ext hab)
  letI : Fintype E.Carrier := Fintype.ofFinite E.Carrier
  have hOldOutside : ∀ b : E.Carrier,
      oldVertex ≠ iOldE b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbComponent : b.1 ∈ functionalComponentFrom
        Forbidden (Set.range d.roots) d.left := hv ▸ hvComponent
    exact b.2 hbComponent
  have hNewAvoidB : ∀ a : Q.Carrier,
      flip (iQ a) ∉ fullFreeRightExclusiveTarget iRight jRight := by
    intro a
    rw [hQImage a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iRight iLeft jRight jLeft hFree.swap (g a)
  have hTargetAgreeR (r : UX) :
      jRight (iRight r) = jLeft (iLeft r) :=
    ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hvRightSwapped :
      oldVertex ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hvRight.1, ?_⟩
    intro hr
    obtain ⟨x, hx⟩ := hr
    apply hvRight.2
    exact ⟨x, (hTargetAgreeR x).symm.trans hx⟩
  have hvRightTarget :
      f oldVertex ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive
      iRight jRight f oldVertex).mp hvRightSwapped
  have hStrictGlobal :
      Nat.card {w : W //
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := iOldE) (iNewL := iQ) (iNewR := iE)
      (sNewL := Q.rootEmbedding) (sRight := E.rootEmbedding)
      hNewFree f flip (fun b : E.Carrier => f b.1)
      (by intro b; rfl) hEImage
      (fullFreeRightExclusiveTarget iRight jRight)
      hNewAvoidB oldVertex hvRightTarget hOldOutside
  have hStrictLocal :
      Nat.card {w : W //
        w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ K ∧ f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    have h :=
      fullFreeAmalgam_contextLocal_support_lt_of_global
        hOldFree hNewFree SR hRootSR f flip
        (fullFreeRightExclusiveTarget iRight jRight)
        hEImage hStrictGlobal
    simpa only [hOldCarrier] using h
  have hOutsideA :
      Nat.card {w : W //
        w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) ∧
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : V //
        v ∉ K ∧ f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    have h :=
      fullFreeAmalgam_contextOutside_support_card_eq
        hOldFree hNewFree SR hRootSR f flip
        (fullFreeLeftExclusiveTarget iLeft jLeft) hEImage
    simpa only [hOldCarrier] using h
  have hNewClosed :
      New.IsClosed
        (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) := by
    have hQclosed : Q.str.IsClosed (Set.univ : Set Q.Carrier) := by
      intro funsym xs hxs y hy
      trivial
    exact fullFreeAmalgam_closed_union_of_closed_sides
      hNewFree (Set.univ : Set Q.Carrier) SR
      hQclosed hSRclosed (fun _ => Set.mem_univ _) hRootSR
  let SOld : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  let SNew : Set W :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) flip
  have hNewRootInS : ∀ i : Fin m, iE (E.rootEmbedding i) ∈ SNew := by
    intro i
    change flip (iE (E.rootEmbedding i)) ∈
      Set.range (jLeft.comp iLeft)
    rw [hEImage (E.rootEmbedding i)]
    change f (d.roots i) ∈ Set.range (jLeft.comp iLeft)
    exact hRoots ⟨i, rfl⟩
  have hSeamAgree : ∀ b : E.Carrier,
      iE b ∈ SNew ↔ iOldE b ∈ SOld := by
    intro b
    change flip (iE b) ∈ Set.range (jLeft.comp iLeft) ↔
      f b.1 ∈ Set.range (jLeft.comp iLeft)
    rw [hEImage b]
  have hOldNoEscape :
      FunctionalContextNoEscapeOutsideSeam Forbidden SOld
        (iOldInner '' (Set.univ : Set Inner.Carrier) ∪
          iOldE '' SR) := by
    rw [hOldCarrier]
    exact hKnoEscape
  have hNewNoEscape :
      FunctionalContextNoEscapeOutsideSeam New SNew
        (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) :=
    fullFreeAmalgam_noEscape_preserved_under_innerReplacement
      hOldFree hNewFree SOld SNew SR
      hNewRootInS hSeamAgree hOldNoEscape
  exact ⟨W, New, hNew, Q, iQ, iE, hNewFree,
    flip, hFlip, hEImage, hNewClosed, hNewNoEscape,
    hStrictLocal, hOutsideA⟩

end AllThoseRamseyClasses.Lifts
