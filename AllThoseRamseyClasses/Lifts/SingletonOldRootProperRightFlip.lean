import AllThoseRamseyClasses.Lifts.SingletonOldRootOppositePiece
import AllThoseRamseyClasses.Lifts.UncoveredMinimalMixedOldRootLoss
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Actual B-to-A flip of a proper sub-piece when the old mixed root is singleton

The unrestricted Section 3 Claim 2 flip-iteration remains open.
There is, however, a meaningful source-matched width-one
subcase (width ONE for the OLD minimal mixed piece P,
NOT necessarily for the new geometric piece's root).

At a finite connected forbidden weak EHN source minimizing
LEFT-exclusive SOURCE support, choose a genuinely smallest
mixed source piece P with a singleton old separator root.
Let x be a right-exclusive source S-component vertex inside
P, y a left-exclusive vertex inside P, and let
T=Cl(N(component(Source minus S,x))) be its full boundary.
Assume the opposite y-component after deleting T does not
cover all of T, and the original weak map is injective
only on the preimage S of the common root.

The verified exact-root source proof constructs a new
minimal-cut piece Q rooted at U=Cl(N(component(Source
minus T,y))) whose LEFT component is mixed and captures
the unique old root of P. The source-only singleton-root
theorem shows that the OPPOSITE orientation of Q has an
entirely RIGHT-sided selected component, strictly inside
P's original selected component, and is an ACTUAL
PROPER sub-piece of P.

Injectivity on S provides injectivity of its root images.
The original FULL quotient-indexed common canonical lift
then produces a LITERAL new forbidden source by flipping
that opposite piece from Right to Left. The new weak EHN
witness to the SAME target has STRICTLY fewer ORIGINAL
right-exclusive SOURCE vertices.

This is a completed one-step elimination of a genuine
proper B-only source piece under explicit width-one old
root hypotheses. It does NOT give an immediate contradiction
to the assumed LEFT-support minimum (the replacement may
increase left support), nor prove preservation of the old
outer mixed piece under repeated flips.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For a genuinely smallest mixed old piece P with a singleton
OLD root, an uncovered right-component boundary yields an
actual PROPER right-only sub-piece of P and its genuine
B-to-A forbidden-source flip, strictly reducing right
source support.

The returned piece's positive-width root is the complete
generated opposite-component boundary U. No target-map
injectivity outside the shared-root preimage is required. -/
theorem minimalLeftSingletonOldRoot_uncovered_hasProperRightFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
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
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hInjOnRoot : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hMinP : ∀ Q : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      P.nonrootCount ≤ Q.nonrootCount)
    (hSingletonOldRoot : ∀ a b : w.Carrier,
      a ∈ Set.range P.data.roots →
      b ∈ Set.range P.data.roots → a = b)
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hxOld : x.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (y : {z : w.Carrier // z ∉ T})
    (hyLeft : y.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (hyOld : y.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left)
    (hUncovered : ¬ T ⊆ w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y))) :
    ∃ (m : ℕ) (Qright : GeometricFunctionalPieceData w.source m),
      0 < m ∧
      Set.range Qright.roots = w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph T y)) ∧
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
            w.toTarget v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  obtain ⟨m, d, r, hm, hExactRoot, _hRootProper,
      hRootInsideP, hLeftY, hRightX, hrOld, hrCaptured, _hrNotU⟩ :=
    minimalLeftWitness_uncoveredInsideMinimalMixed_losesOldRoot
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon w hMinLeft hInjOnRoot
      P hMinP x hxRight hxOld T hT hTS
      y hyLeft hyOld hUncovered
  have hRootS : Set.range d.roots ⊆ S := by
    rw [hExactRoot]
    exact (functionalClosure_neighborhood_subset_cut
      w.source T
      (by
        rw [hT]
        exact w.source.functionClosure_isClosed
          (gaifmanNeighborhood w.source.graph
            (componentFrom w.source.graph S x)))
      y).trans hTS
  have hLeftOld : d.left.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left := by
    rw [hLeftY]
    exact hyOld
  have hRightOld : d.right.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left := by
    rw [hRightX]
    exact hxOld
  have hRightB : d.right.1 ∈ BOnly := by
    rw [hRightX]
    exact hxRight
  obtain ⟨hProperFull, _hProperComp, hNoLeft⟩ :=
    minimalMixedSingletonOldRoot_oppositeComponent_oneSided
      w.source S AOnly BOnly P hMinP hSingletonOldRoot
      d hm hRootS hRootInsideP hLeftOld hRightOld
      hRightB ⟨r, hrOld, hrCaptured⟩
  let Qright : GeometricFunctionalPieceData w.source m := {
    roots := d.roots
    roots_injective := d.roots_injective
    left := d.right
    right := d.left
    minimal := minimalClosedSeparator_swap
      w.source (Set.range d.roots) d.left d.right d.minimal
  }
  have hPieceProper :
      geometricPieceVertices w.source Qright ⊂
        geometricPieceVertices w.source P.data := hProperFull
  have hRootsQ : Set.range Qright.roots = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y)) := hExactRoot
  have hInj :
      Function.Injective (fun i : Fin m =>
        w.toTarget (Qright.roots i)) := by
    intro i j hij
    apply d.roots_injective
    exact hInjOnRoot
      (hRootS ⟨i, rfl⟩) (hRootS ⟨j, rfl⟩) hij
  have hQrightVertex :
      Qright.left.1 ∈ functionalComponentFrom w.source
        (Set.range Qright.roots) Qright.left :=
    functionalComponentFrom_root w.source
      (Set.range Qright.roots) Qright.left
  obtain ⟨V', New, hNew, flip, hFlip, hDrop⟩ :=
    geometricGlobalCommonFullLiftFlip_strict_rightSupport
      F hFiniteF w.source w.finiteCarrier w.forbidden
      Qright hm Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hRootS hNoLeft hInj
      Qright.left.1 hQrightVertex hRightB
  exact ⟨m, Qright, hm, hRootsQ, hPieceProper, hNoLeft,
    V', New, hNew, flip, hFlip, hDrop⟩

end AllThoseRamseyClasses.Lifts
