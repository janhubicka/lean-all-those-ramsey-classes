import AllThoseRamseyClasses.Lifts.Claim2NoTwoSidedRootCaptureAllWidths
import AllThoseRamseyClasses.Lifts.Claim2WidthOnePositiveRankFlip

/-!
# All root widths: eliminate both smaller-root obstructions at an original extremal source

The verified A-support-minimizing original forbidden SOURCE witness
and globally minimum nonroot-size A/B-mixed geometric source piece P
force a captured OLD P-root vertex into the opposite A-side
component of any selected smaller positive root d, provided d's
ordered TARGET root is injective.

The new source boundary localization from PR #1224 shows
that two opposite components of d CANNOT capture different
old P-root source vertices when d.root lies inside old P
and both P and d are genuinely minimal function-closed
source separators. This uses the OLD P.right generated
boundary, NOT a width-one singleton argument.

Hence d.left B-side cannot capture any old P-root at ANY width.
If d.left is also A-mixed, minimal-mixed-piece source
minimality forces precisely such prohibited capture.
Thus BOTH smaller-root alternatives in the verified
positive-B-rank source dichotomy are eliminated.

The positive-rank theorem then provides ONE actual genuine
B-to-A forbidden SOURCE replacement, SAME old global
canonical piece symbol, ordered target-root coordinates,
strict B-exclusive SOURCE decrease inside one new
geometric outer piece, exact exterior SOURCE count
conservation, and surviving real A-exclusive SOURCE anchor.

IMPORTANT: This depends on draft #1224 source geometry,
which is NOT YET LEAN-VERIFIED. Do not claim it resolves
the unrestricted 2019 theorem until that independent
closure/path proof and this corollary both pass.
The output B-flip may increase total A-support, so original
global A-minimality is NOT automatically preserved through
iteration; the exact A-cost gap remains as in #1196/#1206.
The initial mixed-piece state and full section integration
remain separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If P is an original globally minimum-size mixed geometric
piece of an original globally A-source-support-minimal
forbidden weak-map witness, then under exact smaller-root
B/A endpoints and injective TARGET d-root tuple, neither
old-root B-side capture nor A-mixed B-side component
can occur at ANY old root width. -/
theorem claim2_originalAMinimal_allWidths_no_smallerRootObstruction
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
    (hDRootSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hDRootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hDleftB : d.left.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hDrightA : d.right.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hObstruction :
      (∃ r : V, r ∈ Set.range P.data.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left) ∨
      (∃ a : V,
        a ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left ∧
        a ∈ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) f)) : False := by
  letI : Finite V := hFinite
  have hCapture :
      ∃ r : V, r ∈ Set.range P.data.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left := by
    rcases hObstruction with hCapture | hMixed
    · exact hCapture
    · obtain ⟨r, hr, _, hComponent, _⟩ :=
        claim2_minimalMixed_smallerMixed_capturesOldRoot
        Source
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
        (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
        (weakFreeRightPart (sL := iLeft) (iL := jLeft)
          (iR := jRight) f)
        P hMinimal d hm hDRootSeam
        hDleftOld hDrightOld hMixed
        ⟨d.left.1,
          componentFrom_root Source.graph (Set.range d.roots) d.left,
          hDleftB⟩
      exact ⟨r, hr, hComponent⟩
  obtain ⟨rOpposite, hrOld, hrOpposite⟩ :=
    claim2_globalAMinimal_forces_oldRootInOppositeComponent
      F hFiniteF Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      P hMinimal d hm hDRootInsideP hDleftOld hDrightOld
      hDRootSeam hDRootTargetInjective hDrightA hAMinimal
  exact geometric_no_twoSidedOldRootCapture_of_newRoot_inside_oldPiece
    Source P.data d hDRootInsideP hCapture
    ⟨rOpposite, hrOld, hrOpposite⟩


/-- Full positive-rank original all-width conclusion:
the verified actual positive B-source-rank dichotomy
must produce a real old-global-symbol strictly
B-decreasing forbidden SOURCE replacement, rather than
its smaller-root obstruction alternative, under original
extremal witness hypotheses and LOCAL generated
B-active boundary injectivity. -/
theorem claim2_originalAMinimal_allWidths_positiveB_hasActualFlip
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
      (claim2_originalAMinimal_allWidths_no_smallerRootObstruction
        F hFiniteF Source hFinite hForbidden
        Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        P hMinimal d hm hDRootInsideP
        hDleftOld hDrightOld hDRootSeam hInj
        hDleftB hDrightA hAMinimal hObstruction)


end AllThoseRamseyClasses.Lifts
