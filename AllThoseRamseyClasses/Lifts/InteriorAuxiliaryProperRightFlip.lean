import AllThoseRamseyClasses.Lifts.ExteriorBoundaryPreventsRootSplit
import AllThoseRamseyClasses.Lifts.GeneralOldRootCapturedRightPiece

/-!
# Genuine arbitrary-width proper B-side sub-piece from an interior auxiliary cut

For a minimum mixed source piece P=(R,C), let a new genuine closed
separator U be wholly contained in the old piece R∪C. If one old-root
vertex belongs to Q.left, the generated boundary of P's OPPOSITE
component ensures no old-root vertex lies in Q.right, even when the
old root is reducible and has arbitrary width.

The checked escaping-component theorem therefore localizes the entire
Q.right component inside C. Since it excludes Q.left's distinguished
vertex, its nonroot component is strictly smaller than C. At a minimum
mixed P it cannot contain both colours, so if Q.right itself is B-only
the entire opposite rooted source piece is a genuine proper B-only
sub-piece. With injective new target root coordinates, the original
FULL canonical lift supplies an actual forbidden-source B→A flip
strictly decreasing original B-exclusive source support.

These are conditional theorems about actual source geometry; they do
NOT assert existence of U and an old-root capture under the general
printed hypotheses, nor preservation of the outer profile under the
subsequent contextual flip. No weak EHN map is injectivized globally.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A minimum mixed piece has a proper B-only subpiece at arbitrary
old-root width once the new auxiliary separator lies in the old
piece and its other component captures one old-root vertex. -/
theorem minimalMixedInteriorRootCapture_oppositeComponent_oneSided
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinP : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    {m : ℕ}
    (Q : GeometricFunctionalPieceData Source m)
    (hQpositive : 0 < m)
    (hCaptured : ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left)
    (hQrootS : Set.range Q.roots ⊆ S)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices Source P.data)
    (hQleftOld :
      Q.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightB : Q.right.1 ∈ BOnly) :
    (Set.range Q.roots ∪
      functionalComponentFrom Source (Set.range Q.roots) Q.right) ⊂
        geometricPieceVertices Source P.data ∧
      functionalComponentFrom Source (Set.range Q.roots) Q.right ⊂
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left ∧
      ∀ z : V,
        z ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right →
        z ∉ AOnly := by
  let Qswap : GeometricFunctionalPieceData Source m := {
    roots := Q.roots
    roots_injective := Q.roots_injective
    left := Q.right
    right := Q.left
    minimal := minimalClosedSeparator_swap
      Source (Set.range Q.roots) Q.left Q.right Q.minimal
  }
  have hRightSubset :
      functionalComponentFrom Source (Set.range Q.roots) Q.right ⊆
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left :=
    geometricPiece_opposite_localized_of_innerCutRootCapture
      Source P.data Q hQrootInsideP hCaptured hQrightOld
  have hLeftNotRight :
      Q.left.1 ∉ functionalComponentFrom Source
        (Set.range Q.roots) Q.right := by
    intro hLeftInRight
    have hInLeft :=
      functionalComponentFrom_root Source
        (Set.range Q.roots) Q.left
    exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint Source Q))
      hInLeft hLeftInRight
  have hRightProper :
      functionalComponentFrom Source (Set.range Q.roots) Q.right ⊂
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hRightSubset, ?_⟩
    intro hEq
    apply hLeftNotRight
    rw [hEq]
    exact hQleftOld
  have hNoLeft :
      ∀ z : V,
        z ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right →
        z ∉ AOnly := by
    intro z hzRight hzA
    let M : MixedGeometricPiece Source S AOnly BOnly := {
      width := m
      data := Qswap
      positive := hQpositive
      roots_in_common := hQrootS
      left_mixed := ⟨z, hzRight, hzA⟩
      right_mixed := ⟨Q.right.1,
        functionalComponentFrom_root Source
          (Set.range Q.roots) Q.right, hQrightB⟩
    }
    exact minimalMixedGeometricPiece_no_proper_mixed_component
      P hMinP M hRightProper
  have hPieceProper :
      geometricPieceVertices Source Qswap ⊂
        geometricPieceVertices Source P.data :=
    geometricPiece_proper_subpiece_of_rightInOldComponent
      Source P.data Qswap hQrootInsideP hRightSubset hQleftOld
  have hFullProper :
      (Set.range Q.roots ∪
        functionalComponentFrom Source
          (Set.range Q.roots) Q.right) ⊂
      geometricPieceVertices Source P.data := hPieceProper
  exact ⟨hFullProper, hRightProper, hNoLeft⟩


/-- The resulting genuine one-sided sub-piece admits the certified
original-global B-to-A replacement with strict RIGHT-exclusive
source-support decrease when its ordered target roots are injective. -/
theorem minimalMixedInteriorRootCapture_hasProperRightFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hMinP : ∀ D : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      P.nonrootCount ≤ D.nonrootCount)
    {m : ℕ}
    (Q : GeometricFunctionalPieceData w.source m)
    (hQpositive : 0 < m)
    (hCaptured : ∃ r : w.Carrier,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom w.source (Set.range Q.roots) Q.left)
    (hQrootS : Set.range Q.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices w.source P.data)
    (hQleftOld :
      Q.left.1 ∈ functionalComponentFrom w.source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom w.source
        (Set.range P.data.roots) P.data.left)
    (hQrightB : Q.right.1 ∈
      weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hNewRootImagesInjective :
      Function.Injective (fun i : Fin m => w.toTarget (Q.roots i))) :
    ∃ Qright : GeometricFunctionalPieceData w.source m,
      geometricPieceVertices w.source Qright ⊂
        geometricPieceVertices w.source P.data ∧
      (∀ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range Qright.roots) Qright.left →
        z ∉ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) w.toTarget) ∧
      ∃ (V' : Type) (New : Structure L V'),
        F New ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          Nat.card {v : V' //
            flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : w.Carrier //
            w.toTarget v ∈ fullFreeRightExclusiveTarget
              iRight jRight} := by
  let Qright : GeometricFunctionalPieceData w.source m := {
    roots := Q.roots
    roots_injective := Q.roots_injective
    left := Q.right
    right := Q.left
    minimal := minimalClosedSeparator_swap
      w.source (Set.range Q.roots) Q.left Q.right Q.minimal
  }
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨hProper, _hProperComp, hNoLeft⟩ :=
    minimalMixedInteriorRootCapture_oppositeComponent_oneSided
      w.source S AOnly BOnly P hMinP Q hQpositive
      hCaptured hQrootS hQrootInsideP
      hQleftOld hQrightOld hQrightB
  have hQrightComp :
      Qright.left.1 ∈ functionalComponentFrom w.source
        (Set.range Qright.roots) Qright.left :=
    functionalComponentFrom_root w.source
      (Set.range Qright.roots) Qright.left
  obtain ⟨V', New, hNew, flip, hFlip, hStrict⟩ :=
    geometricGlobalCommonFullLiftFlip_strict_rightSupport
      F hFiniteF w.source w.finiteCarrier w.forbidden
      Qright hQpositive Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hQrootS hNoLeft hNewRootImagesInjective
      Qright.left.1 hQrightComp hQrightB
  exact ⟨Qright, hProper, hNoLeft,
    V', New, hNew, flip, hFlip, hStrict⟩


end AllThoseRamseyClasses.Lifts
