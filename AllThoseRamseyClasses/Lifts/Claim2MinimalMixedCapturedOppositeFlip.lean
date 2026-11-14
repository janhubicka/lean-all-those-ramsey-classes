import AllThoseRamseyClasses.Lifts.Claim2WidthOneCapturedOppositeLeftFlip
import AllThoseRamseyClasses.Lifts.RootRetentionLocalization

/-!
# Global smallest mixed piece eliminates B-mixedness of the opposite captured component

Suppose a genuine smaller minimal closed separator d has both
distinguished endpoints in a globally minimum-nonroot-size mixed
source piece P. If ALL old P-root source vertices belong to
d's selected component, then d's OPPOSITE component is B-free,
provided its distinguished vertex d.right is A-exclusive.

Indeed, a B-exclusive source vertex in that opposite component
would make the genuinely swapped opposite separator into another
A/B-mixed piece rooted in the same full seam. Minimal-mixed-piece
root capture would then force an OLD P-root vertex into the opposite
component. But all old roots were already in d's original component
and genuine minimal-separator components are disjoint.

Hence the previous conditional opposite A-to-B flip becomes available
under global source mixed-piece minimality, without separately
postulating B-purity. This proves a conditional original-source
A-support reduction, NOT the complete original 2019 Claim 2:
all-old-root capture and the injective d-root target tuple remain
explicit premises, and partial capture of multiple old roots
still needs separate analysis.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If the original P is globally minimum among all genuinely
mixed source pieces rooted in S, and d's original selected
component captures EVERY old P-root source vertex, then the
OPPOSITE d-component contains NO BOnly source vertex when
d.right is AOnly.

This is an intrinsic finite SOURCE fact. It needs neither
a weak target map nor a full native target free amalgam. -/
theorem claim2_minimalMixed_allOldRootsCaptured_oppositeBFree
    {V : Type} [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDRootSeam : Set.range d.roots ⊆ S)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hAllOldRootsCapturedLeft :
      Set.range P.data.roots ⊆
        functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (hDrightA : d.right.1 ∈ AOnly) :
    ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right →
      z ∉ BOnly := by
  intro z hzRight hzB
  let opposite := geometricOppositeMinimalSeparatorPiece Source d
  have hDrightInOpposite :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range opposite.roots) opposite.left :=
    componentFrom_root Source.graph (Set.range d.roots) d.right
  let Q : MixedGeometricPiece Source S AOnly BOnly := {
    width := m
    data := opposite
    positive := hm
    roots_in_common := hDRootSeam
    left_mixed := ⟨d.right.1, hDrightInOpposite, hDrightA⟩
    right_mixed := ⟨z, hzRight, hzB⟩
  }
  obtain ⟨r, hrOld, hrOpposite⟩ :=
    minimalMixedPiece_otherMixed_capturesOldRoot
      Source S AOnly BOnly P Q hMinimal hDrightOld hDleftOld
  exact (Set.disjoint_left.mp
    (geometricPiece_components_disjoint Source d))
      (hAllOldRootsCapturedLeft hrOld) hrOpposite

/-- Under the original finite forbidden-source and common FULL
canonical-lift hypotheses, a globally smallest A/B-mixed
old geometric piece P admits a REAL A-support-reducing native
source flip if a smaller root d has its entire old P-root
captured on the B side and injective TARGET root coordinates.

The opposite component's B-freeness is DERIVED from global
minimality, not an independent assumption. The genuine opposite
rooted piece is strictly contained in P and has an actual weak
EHN LEFT-side factorization. This does not rely on root width one. -/
theorem claim2_minimalMixed_allCaptured_opposite_actualLeftSupportFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (P : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f))
    (hMinimal : ∀ Q : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f),
      P.nonrootCount ≤ Q.nonrootCount)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDRootInsideP :
      Set.range d.roots ⊆ geometricPieceVertices Source P.data)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hAllOldRootsCapturedLeft :
      Set.range P.data.roots ⊆
        functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (hDRootSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hDRootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hDrightA : d.right.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f) :
    geometricPieceVertices Source
      (geometricOppositeMinimalSeparatorPiece Source d) ⊂
      geometricPieceVertices Source P.data ∧
    ∃ (W : Type) (New : Structure L W) (hNew : F New)
      (flip : W → UT),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      Nat.card {w : W //
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  letI : Finite V := hFinite
  let opposite := geometricOppositeMinimalSeparatorPiece Source d
  have hProper :
      geometricPieceVertices Source opposite ⊂
        geometricPieceVertices Source P.data :=
    geometricOppositePiece_proper_of_allOldRootsCaptured
      Source P.data d hDRootInsideP hDleftOld hDrightOld
      hAllOldRootsCapturedLeft
  have hNoRight : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
    claim2_minimalMixed_allOldRootsCaptured_oppositeBFree
      Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f)
      P hMinimal d hm hDRootSeam hDleftOld hDrightOld
      hAllOldRootsCapturedLeft hDrightA
  obtain ⟨pLeft, hpLeft, hPieceMap⟩ :=
    weakGeometricPiece_factor_left_if_no_right
      hFree f hf opposite hDRootSeam hNoRight
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
      pLeft hPieceMap' hDRootSeam
  have hRootInj :
      Function.Injective (fun i : Fin m => f (opposite.roots i)) :=
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
