import AllThoseRamseyClasses.Lifts.Claim2WidthOneNoSmallerObstruction
import AllThoseRamseyClasses.Lifts.Claim2PositiveRankRefinedObstructions

/-!
# Positive B-source rank gives a real old-symbol flip for a width-one mixed root

The already verified source-local Claim 2 dichotomy, assuming
complete generated B-active boundary injectivity on an actual
selected geometric outer piece P, returns an actual original
same-symbol B-to-A source flip OR a genuine smaller positive
minimal separator d with one of two precise source obstructions:
  * d.left/B-component captures an old P-root source vertex;
  * d.left/B-component contains a genuine A-exclusive source vertex.

At a finite ORIGINAL F-forbidden weak EHN witness chosen GLOBAL
minimum A-exclusive SOURCE support, with P globally MINIMUM
NONROOT source size among genuine A/B-mixed pieces rooted
in the common full target seam, the new width-one obstruction
exclusion theorem rules out BOTH alternatives for P.width=1.

The output is a REAL strictly B-exclusive-SOURCE-rank-decreasing
original forbidden source flip with the SAME old global
canonical symbol, ordered target root coordinates, every
exterior target-set SOURCE count and a surviving A-only SOURCE
anchor. The result is conditional on an already prepared
A-anchored positive B-state with LOCAL boundary injectivity;
it does not show the resulting new source map is itself
globally minimum A-support, so it does NOT yet provide a
well-founded global B-rank iteration or the 2019 terminal
A-clearing contradiction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the exact original A-minimal and globally smallest-mixed
finite-source hypotheses, every locally B-boundary-injective
POSITIVE B-rank width-one mixed state has a GENUINE selected
B-to-A source flip. No selected smaller-root obstruction
is left at width one.

This does not claim that the new weak EHN witness still realizes
the global original A-support minimum or has the same A-support. -/
theorem claim2_originalAMinimal_widthOne_positiveB_hasActualFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
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
    (hWidthOne : P.width = 1)
    (a : V)
    (haK : a ∈ geometricPieceVertices Source P.data)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositiveB : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P.data ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight})
    (hActiveBoundaryInjective :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P.data →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))))
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P.data ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New P.width),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin P.width,
          flip (newOuter.roots i) = f (P.data.roots i)) ∧
        geometricGlobalPieceSymbol F Source
          hFinite hForbidden P.data P.positive =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter P.positive ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Source P.data ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Source P.data ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft) := by
  rcases
      (claim2_positiveRank_actualFlip_or_capturedRoot_or_mixedComponent
        F hFiniteF hConnected Source hFinite hForbidden
        P.data P.positive Target f hf
        Left Right jLeft jRight X iLeft iRight
        hFree hCommon P.roots_in_common
        a haK haLeft hPositiveB hActiveBoundaryInjective) with
    hFlip | ⟨x, T, m, d, hxK, hxRight, hT, hm,
      hProper, hRootIn, hLeft, hRight, hInj, hObstruction⟩
  · exact hFlip
  · have hxOuter :
        x.1 ∈ functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      rcases hxK with hRoot | hComp
      · obtain ⟨i, hi⟩ := hRoot
        have hxSeam : x.1 ∈
            weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
          hi ▸ P.roots_in_common ⟨i, rfl⟩
        exact False.elim (x.2 hxSeam)
      · exact hComp
    have haOuter :
        a ∈ functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      rcases haK with hRoot | hComp
      · obtain ⟨i, hi⟩ := hRoot
        have haSeam : a ∈
            weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
          hi ▸ P.roots_in_common ⟨i, rfl⟩
        exact False.elim (haLeft.2 haSeam)
      · exact hComp
    have hDleftOld :
        d.left.1 ∈ functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      rw [hLeft]
      exact hxOuter
    have hDrightOld :
        d.right.1 ∈ functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      rw [hRight]
      exact haOuter
    have hDleftB : d.left.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
      rw [hLeft]
      exact hxRight
    have hDrightA : d.right.1 ∈ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) f := by
      rw [hRight]
      exact haLeft
    have hDRootInsideP :
        Set.range d.roots ⊆
          geometricPieceVertices Source P.data := by
      intro z hz
      exact (hRootIn hz).2
    have hDRootSeam : Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f := by
      intro z hz
      exact (hRootIn hz).1
    exact False.elim
      (claim2_originalAMinimal_widthOne_no_smallerRootObstruction
        F hFiniteF Source hFinite hForbidden
        Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        P hMinimal hWidthOne d hm hDRootInsideP
        hDleftOld hDrightOld hDRootSeam hInj
        hDleftB hDrightA hAMinimal hObstruction)

end AllThoseRamseyClasses.Lifts
