import AllThoseRamseyClasses.Lifts.Claim2MinimalMixedCapturedOppositeFlip

/-!
# Opposite-side B-purity under NO opposite old-root capture

The complete-old-root-capture hypothesis can be weakened
substantially. For a globally minimal ORIGINAL A/B-mixed
finite source piece P, a smaller positive root d whose
distinguished endpoints both lie in P's old selected component
and whose root lies in the SAME full seam has this property:

If d.right is A-exclusive, then EITHER its opposite selected
component contains an old P-root SOURCE vertex, OR that opposite
component is B-FREE. Proof: a B-exclusive source vertex in the
opposite component would make the truly swapped minimal-separator
piece A/B-mixed. Global minimum nonroot size then forces an
old P-root into that opposite component.

When the opposite component contains NO old P root, the genuine
opposite geometric piece also stays PROPERLY inside P, by the
already-verified source path escape=>capture lemma. Hence the
conditional original A-support-decreasing global left flip
applies to that genuine nested opposite piece, provided the
smaller d-root has injective target coordinates.

This works even if only SOME old P-root vertices are captured
by the original d.left/B component: complete capture is not
necessary. Still unresolved: an old P-root captured by BOTH
selected sides (different vertices in different components),
plus all other original 2019 terminal/normalization obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under global nonroot-size minimality among A/B-mixed true
source pieces, a positive smaller native root with no old P-root
vertex in its OPPOSITE d.right component has a GENUINE properly
nested opposite geometric piece whose selected component is B-free.

No assumption about how many old P-roots are captured in
d.left; the old root may be partially captured on that side. -/
theorem claim2_minimalMixed_noOppositeOldRoot_proper_and_BFree
    {V : Type} [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDRootInsideP :
      Set.range d.roots ⊆ geometricPieceVertices Source P.data)
    (hDRootSeam : Set.range d.roots ⊆ S)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hNoOppositeOldRoot :
      ∀ r : V, r ∈ Set.range P.data.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.right)
    (hDrightA : d.right.1 ∈ AOnly) :
    geometricPieceVertices Source
      (geometricOppositeMinimalSeparatorPiece Source d) ⊂
      geometricPieceVertices Source P.data ∧
    ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right →
      z ∉ BOnly := by
  classical
  let opposite := geometricOppositeMinimalSeparatorPiece Source d
  have hOppComponentInsideP :
      functionalComponentFrom Source
        (Set.range opposite.roots) opposite.left ⊆
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left := by
    by_contra hEscape
    obtain ⟨r, hrOld, hrOpp⟩ :=
      geometricPiece_escapingComponent_capturesOldRoot
        Source P.data opposite hDrightOld hEscape
    exact hNoOppositeOldRoot r hrOld hrOpp
  have hProper :
      geometricPieceVertices Source opposite ⊂
        geometricPieceVertices Source P.data :=
    geometricPiece_proper_subpiece_of_rightInOldComponent
      Source P.data opposite hDRootInsideP
      hOppComponentInsideP hDleftOld
  have hBFree : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right → z ∉ BOnly := by
    intro z hzBComp hzBOnly
    have hDrightComp :
        d.right.1 ∈ functionalComponentFrom Source
          (Set.range opposite.roots) opposite.left :=
      componentFrom_root Source.graph (Set.range d.roots) d.right
    let Q : MixedGeometricPiece Source S AOnly BOnly := {
      width := m
      data := opposite
      positive := hm
      roots_in_common := hDRootSeam
      left_mixed := ⟨d.right.1, hDrightComp, hDrightA⟩
      right_mixed := ⟨z, hzBComp, hzBOnly⟩
    }
    obtain ⟨r, hrOld, hrOpp⟩ :=
      minimalMixedPiece_otherMixed_capturesOldRoot
        Source S AOnly BOnly P Q hMinimal hDrightOld hDleftOld
    exact hNoOppositeOldRoot r hrOld hrOpp
  exact ⟨hProper, hBFree⟩

/-- With the original full target free amalgam and common FULL
global canonical lift, global mixed-piece minimality and the
absence of OLD-root vertices in d's opposite component suffice
for a REAL source A-to-B flip strictly reducing A-exclusive
SOURCE support.

Unlike the complete-capture predecessor, this allows arbitrary
old-root distribution elsewhere, including PARTIAL capture in
d.left; only the opposite component must avoid old roots. -/
theorem claim2_minimalMixed_noOppositeOldRoot_actualLeftSupportFlip
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
    (hNoOppositeOldRoot :
      ∀ r : V, r ∈ Set.range P.data.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.right)
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
  obtain ⟨hProper, hNoRight⟩ :=
    claim2_minimalMixed_noOppositeOldRoot_proper_and_BFree
      Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f)
      P hMinimal d hm hDRootInsideP hDRootSeam
      hDleftOld hDrightOld hNoOppositeOldRoot hDrightA
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
