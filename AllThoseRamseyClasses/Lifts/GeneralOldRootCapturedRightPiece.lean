import AllThoseRamseyClasses.Lifts.SingletonOldRootOppositePiece
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# Arbitrary-width old-root capture gives a proper B-only opposite sub-piece

The verified singleton-old-root argument uses cardinality one only
to rule out a split of the old separating root between TWO distinct
components of a newly selected smaller-root source piece Q.

That graph argument has an exact arbitrary-width strengthening:
it suffices for the ENTIRE old root of a minimum mixed piece P to
belong to Q's left selected nonroot component. Then Q's opposite
right component cannot capture ANY old root vertex because the two
components of Source minus the new root are disjoint.

The existing checked escaping-component lemma then places the
opposite component fully inside the original selected old
component. Minimality of the mixed nonroot count forces it
right-only. Its whole closed root and selected component form an
ACTUAL PROPER sub-piece of P. No new target quotient, root-image
injection or width-one restriction is used.

This isolates the remaining general-width obstruction sharply:
the uncovered-boundary construction may split distinct old root
vertices between different new components. Handling that split,
rather than simply extending singleton-root cardinality, is the
open geometric step of the 2019 Claim 2 proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Under the genuine minimum mixed nonroot cardinality, an
arbitrary-width old separator captured ENTIRELY by one side of
a new actual geometric source piece forces the opposite
orientation to be a proper one-sided B-piece.

Root capture is an explicit source-Gaifman condition; it is
not derived from all-test profiles or target injectivity. -/
theorem minimalMixedCapturedEntireOldRoot_oppositeComponent_oneSided
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinP : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    {m : ℕ}
    (Q : GeometricFunctionalPieceData Source m)
    (hQpositive : 0 < m)
    (hAllOldRootsCapturedLeft :
      Set.range P.data.roots ⊆
        functionalComponentFrom Source
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
  have hNoOldRootInQRight :
      Disjoint (Set.range P.data.roots)
        (functionalComponentFrom Source
          (Set.range Q.roots) Q.right) := by
    apply Set.disjoint_left.mpr
    intro z hzOld hzRight
    exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint Source Q))
      (hAllOldRootsCapturedLeft hzOld) hzRight
  have hRightSubset :
      functionalComponentFrom Source (Set.range Q.roots) Q.right ⊆
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
    by_contra hEscape
    have hEscapeSwap :
        ¬ functionalComponentFrom Source
            (Set.range Qswap.roots) Qswap.left ⊆
          functionalComponentFrom Source
            (Set.range P.data.roots) P.data.left := hEscape
    obtain ⟨rEscape, hrEscapeOld, hrEscapeRight⟩ :=
      geometricPiece_escapingComponent_capturesOldRoot
        Source P.data Qswap hQrightOld hEscapeSwap
    exact (Set.disjoint_left.mp hNoOldRootInQRight)
      hrEscapeOld hrEscapeRight
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

/-- Under the same arbitrary-old-width FULL root-capture
condition, the now-proved genuine proper B-only source
sub-piece can be flipped by the ORIGINAL full canonical
lift into the left target side.

The new actual finite forbidden source has a weak EHN map
into the same target with strictly fewer ORIGINAL
right-exclusive SOURCE vertices. Only the chosen new
piece's ordered target-root images are assumed injective.
No global target-map injection or singleton old-root
hypothesis occurs.

This is a complete conditional general-width one-step
Claim 2 flip. The condition that all old root vertices
are captured on one side remains the unproved bridge in
the arbitrary-width uncovered-boundary case. -/
theorem minimalMixedCapturedEntireOldRoot_hasProperRightFlip
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
    (hAllOldRootsCapturedLeft :
      Set.range P.data.roots ⊆
        functionalComponentFrom w.source (Set.range Q.roots) Q.left)
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
    minimalMixedCapturedEntireOldRoot_oppositeComponent_oneSided
      w.source S AOnly BOnly P hMinP Q hQpositive
      hAllOldRootsCapturedLeft hQrootS hQrootInsideP
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
