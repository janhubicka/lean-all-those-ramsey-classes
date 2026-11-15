import AllThoseRamseyClasses.Lifts.Claim2OppositeSideNestingAfterCapture
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates

/-!
# A conditional original-2019 A-support exit from width-one root capture

When a genuine smaller native separator d captures the sole root of
the old width-one geometric outer piece P in its d.left component,
the OPPOSITE d.right component is properly nested in P and becomes
a GENUINE minimal-closed-separator geometric piece with the same
complete new root.

If the d.right component is entirely B-free relative to the ACTUAL
target free amalgam, its genuine piece weak EHN map factors through
the LEFT target side. If its ordered root has INJECTIVE target images,
the verified global common-canonical-lift left-to-right source flip
therefore yields a REAL new forbidden source and weak EHN map with
strictly LESS A-exclusive SOURCE support.

This is the precise conditional source-flip response to one captured
old-root pattern. It does not assert B-freeness of the opposite
component or target-root injectivity without a proof. Global original
A-support minimality, if available, would contradict the produced
strict decrease. No opposite-side canonical relation equality is
asserted for the original outer P.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An old WIDTH-ONE capture by d.left admits a valid reverse
A-to-B forbidden-source flip if the genuine opposite component
is B-free and its complete ordered root has injective TARGET
coordinates.

The output new forbidden source has strictly smaller A-exclusive
SOURCE vertex cardinality, and the entire opposite native
minimal-separator piece was properly nested inside P. -/
theorem claim2_widthOne_capture_oppositePure_has_actualLeftSupportFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {m : ℕ}
    (P : GeometricFunctionalPieceData Source 1)
    (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDrootInsideP :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hCapture : ∃ r : V, r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hDRootSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hDRootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hOppositeNoB : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hDrightA : d.right.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f) :
    geometricPieceVertices Source
      (geometricOppositeMinimalSeparatorPiece Source d) ⊂
      geometricPieceVertices Source P ∧
    ∃ (W : Type) (New : Structure L W) (hNew : F New)
        (flip : W → UT),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      Nat.card {w : W //
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  let opposite := geometricOppositeMinimalSeparatorPiece Source d
  have hProper :
      geometricPieceVertices Source opposite ⊂
        geometricPieceVertices Source P :=
    geometricOppositePiece_widthOne_capture_proper
      Source P d hDrootInsideP hDleftOld hDrightOld hCapture
  have hRoot :
      Set.range opposite.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
    hDRootSeam
  have hNoRight : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range opposite.roots) opposite.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
    hOppositeNoB
  obtain ⟨pLeft, hpLeft, hPieceMap⟩ :=
    weakGeometricPiece_factor_left_if_no_right
      hFree f hf opposite hRoot hNoRight
  have hpLeft' :
      Structure.IsEHNHomomorphismEmbedding
        (geometricGlobalFunctionalChart Source opposite).ext.str
        Left pLeft := hpLeft
  have hPieceMap' :
      ∀ z : (geometricGlobalFunctionalChart Source opposite).ext.Carrier,
        jLeft (pLeft z) = f z.1 := hPieceMap
  obtain ⟨xsX, hRootLeft⟩ :=
    geometricPiece_commonRootCoordinates
      Source opposite Target f X Left iLeft jLeft
      pLeft hPieceMap' hRoot
  have hRootInj :
      Function.Injective
        (fun i : Fin m => f (opposite.roots i)) :=
    hDRootTargetInjective
  have hAComp :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range opposite.roots) opposite.left :=
    componentFrom_root Source.graph (Set.range d.roots) d.right
  obtain ⟨W, New, hNew, flip, hFlip, hStrictA⟩ :=
    geometricGlobalCommonFullLiftFlip_strict_leftSupport
      F hFiniteF Source hFinite hForbidden opposite hm
      Target f hf
      Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      pLeft hpLeft' hPieceMap' xsX hRootLeft
      hRootInj d.right.1 hAComp hDrightA
  exact ⟨hProper, W, New, hNew, flip, hFlip, hStrictA⟩

end AllThoseRamseyClasses.Lifts
