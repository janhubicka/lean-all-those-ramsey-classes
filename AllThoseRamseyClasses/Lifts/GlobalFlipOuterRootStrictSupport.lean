import AllThoseRamseyClasses.Lifts.GlobalFlipOuterRootPreservation
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# One literal B-to-A forbidden-source replacement with strict support drop
# AND unchanged outer root coordinates

The verified full original-global flip returns a NEW forbidden source,
a FULL embedding of the entire old functional complement, and an
EHN target map agreeing with the old source map on that complement.
The separate support lemma proves a strict global right-support drop.

Here both conclusions are established for the SAME new forbidden
source and SAME new weak map. In particular, the original outer
root tuple survives injectively, with all target coordinates fixed,
provided it lies outside the selected inner nonroot component.

No claim is made that the transported outer root is still a
MINIMAL separator in the new source, or that its outer piece
retains its original global incompatibility class. These remain
the contextual flip obligations of the printed Section 3 Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The SAME actual B-to-A forbidden-source flip strictly lowers
original RIGHT-exclusive SOURCE support, preserves the complete
native functional complement by a FULL embedding, and transports
all ordered outer root vertices injectively with precisely their
original weak-map target coordinates.

Only injection of the INNER flipped root's target images is needed,
not a global injection of the forbidden-source weak EHN map. -/
theorem geometricGlobalRightFlip_outerRoot_and_strictRightSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Forbidden n)
    (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ (iComplement : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New)
        (flip : V' → UT),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
          flip (iComplement b) = f b.1) ∧
        ∃ rootAfter : Fin n → V',
          Function.Injective rootAfter ∧
          (∀ i : Fin n,
            flip (rootAfter i) = f (P.roots i)) ∧
          Nat.card {v : V' //
            flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  classical
  let Compl := geometricGlobalComplementChart Forbidden d
  obtain ⟨Q, _hEquivalent, g, _hg,
      V', New, hNew, iQ, iT, hNewFree,
      flip, hFlip, hQImage, hTImage⟩ :=
    geometricGlobalCommonFullLiftFlip_rightToLeft
      F Forbidden hFinite hForbidden
      d hm Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hInnerRoots hInnerNoLeft
      hInnerRootInjective
  let rootAfter : Fin n → V' :=
    fun i => iT
      (⟨P.roots i, hOuterRootOutside i⟩ : Compl.Carrier)
  have hRootAfterInjective : Function.Injective rootAfter := by
    intro i j hij
    apply P.roots_injective
    have hSame :
        (⟨P.roots i, hOuterRootOutside i⟩ : Compl.Carrier) =
        ⟨P.roots j, hOuterRootOutside j⟩ :=
      iT.injective hij
    exact congrArg Subtype.val hSame
  have hRootAfterTargets :
      ∀ i : Fin n, flip (rootAfter i) = f (P.roots i) := by
    intro i
    exact hTImage
      (⟨P.roots i, hOuterRootOutside i⟩ : Compl.Carrier)

  let oldCompl : Structure.Embedding Compl.str Forbidden :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite V' := hFiniteF New hNew
  letI : Fintype V' := Fintype.ofFinite V'
  letI : Finite Compl.Carrier :=
    Finite.of_injective (fun b : Compl.Carrier => b.1) (by
      intro a b hab
      exact Subtype.ext hab)
  letI : Fintype Compl.Carrier := Fintype.ofFinite Compl.Carrier
  have hOldComplement : ∀ b : Compl.Carrier,
      f (oldCompl b) = f b.1 := by
    intro b
    rfl
  have hOldOutside : ∀ b : Compl.Carrier,
      oldVertex ≠ oldCompl b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbComponent : b.1 ∈
        functionalComponentFrom Forbidden (Set.range d.roots)
          d.left := hv ▸ hvComponent
    exact b.2 hbComponent
  have hNewPieceAvoid : ∀ a : Q.Carrier,
      flip (iQ a) ∉ fullFreeRightExclusiveTarget iRight jRight := by
    intro a
    rw [hQImage a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iRight iLeft jRight jLeft hFree.swap (g a)
  have hTargetAgreeR (r : UX) :
      jRight (iRight r) = jLeft (iLeft r) := by
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
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
  have hStrict :
      Nat.card {v : V' //
        flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := oldCompl)
      (iNewL := iQ)
      (iNewR := iT)
      (sNewL := Q.rootEmbedding)
      (sRight := Compl.rootEmbedding)
      hNewFree f flip (fun b : Compl.Carrier => f b.1)
      hOldComplement hTImage
      (fullFreeRightExclusiveTarget iRight jRight)
      hNewPieceAvoid oldVertex hvRightTarget hOldOutside
  exact ⟨V', New, hNew, iT, flip, hFlip, hTImage,
    rootAfter, hRootAfterInjective, hRootAfterTargets, hStrict⟩

end AllThoseRamseyClasses.Lifts
