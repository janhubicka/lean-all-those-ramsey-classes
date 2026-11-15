import AllThoseRamseyClasses.Lifts.Claim2SmallerRootTargetTupleInjective
import AllThoseRamseyClasses.Lifts.Claim2SmallerRootExhaustiveObstructions

/-!
# Positive B-rank: actual flip or two explicit geometric obstructions

From the verified positive-rank active-boundary dichotomy, the exact
target-root injectivity of the smaller closed separator, and the
exhaustive no-capture/no-A-mixed flip classification, derive a
sharper ORIGINAL SOURCE statement.

An A-anchored positive-B-rank forbidden source with local generated
B-boundary injection either has an actual old-symbol B-source-rank
decreasing flip preserving all exterior SOURCE counts and a genuine
A-only anchor, OR the selected smaller closed separator d has
one of TWO explicit obstructions:
  (1) its chosen component captures a vertex of the OLD outer root;
  (2) its chosen component itself contains an A-exclusive SOURCE vertex.

The obstructing d has an actual positive complete native closed
separator root lying inside the B-generated boundary T, mapped
injectively to target and contained in the full target seam and old P.
No new weak-map quotient, whole-seam injection, or root-width decrease.
The theorem does NOT eliminate either obstruction; original Claim 2
and terminal A-clearing still require further work.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- On every positive B-rank A-anchored state, either a true finite
forbidden source flip with strict B-source descent exists, or one
of exactly the two remaining selected-smaller-root geometric
obstructions is witnessed in the SAME original source. -/
theorem claim2_positiveRank_actualFlip_or_capturedRoot_or_mixedComponent
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
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
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (a : V)
    (haK : a ∈ geometricPieceVertices Source P)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositiveB : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight})
    (hActiveBoundaryInjective :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
    (∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin n, flip (newOuter.roots i) = f (P.roots i)) ∧
        geometricGlobalPieceSymbol F Source
            hFinite hForbidden P hn =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter hn ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Source P ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Source P ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft)) ∨
    (∃ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
        (T : Set V) (m : ℕ)
        (d : GeometricFunctionalPieceData Source m),
      x.1 ∈ geometricPieceVertices Source P ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      0 < m ∧
      Set.range d.roots ⊂ T ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩
          geometricPieceVertices Source P ∧
      d.left.1 = x.1 ∧ d.right.1 = a ∧
      Function.Injective (fun i : Fin m => f (d.roots i)) ∧
      ((∃ r : V, r ∈ Set.range P.roots ∧
          r ∈ functionalComponentFrom Source
            (Set.range d.roots) d.left) ∨
       (∃ z : V, z ∈ functionalComponentFrom Source
            (Set.range d.roots) d.left ∧
          z ∈ weakFreeLeftPart
            (sL := iLeft) (iL := jLeft) f))) := by
  classical
  rcases
      (claim2_positiveRank_actualSuccessor_or_smallerRoot_withTargetRootInj_of_activeBoundaryInjective
        F hFiniteF hConnected Source hFinite hForbidden
        P hn Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon hOuterRootInSeam
        a haK haLeft hPositiveB hActiveBoundaryInjective) with
    hFlip | ⟨x, T, y, m, d, hxK, hxRight, hYa, hT,
      hm, hProper, hRootIn, hLeft, hRight, hExactRoot, hInjective⟩
  · exact Or.inl hFlip
  · have hxOuter :
        x.1 ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rcases hxK with hRoot | hComp
      · obtain ⟨i, hi⟩ := hRoot
        have hxSeam : x.1 ∈
            weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
          hi ▸ hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (x.2 hxSeam)
      · exact hComp
    have haOuter :
        a ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rcases haK with hRoot | hComp
      · obtain ⟨i, hi⟩ := hRoot
        have haSeam : a ∈
            weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
          hi ▸ hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (haLeft.2 haSeam)
      · exact hComp
    have hDleftInOld :
        d.left.1 ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rw [hLeft]
      exact hxOuter
    have hDrightInOld :
        d.right.1 ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rw [hRight]
      exact haOuter
    have hDleftB : d.left.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
      rw [hLeft]
      exact hxRight
    have hDrightA : d.right.1 ∈
        weakFreeLeftPart (sL := iLeft) (iL := jLeft) f := by
      rw [hRight]
      exact haLeft
    rcases
        (claim2_smallerRoot_capture_or_mixed_or_actualGeometricFlip
          F hFiniteF Source hFinite hForbidden
          P d hm hn
          (fun z hz => (hRootIn hz).2)
          hDleftInOld hDrightInOld
          Target f hf Left Right jLeft jRight
          X iLeft iRight hFree hCommon
          (fun z hz => (hRootIn hz).1)
          hInjective hDleftB hDrightA) with
      hCapture | hMixed | hInnerFlip
    · exact Or.inr ⟨x, T, m, d, hxK, hxRight, hT,
        hm, hProper, hRootIn, hLeft, hRight, hInjective,
        Or.inl hCapture⟩
    · exact Or.inr ⟨x, T, m, d, hxK, hxRight, hT,
        hm, hProper, hRootIn, hLeft, hRight, hInjective,
        Or.inr hMixed⟩
    · obtain ⟨hInnerProper, V', New, hNew, hFiniteNew,
        flip, newOuter, hEHN, hCoords, hSymbol,
        hStrictB, hExterior,
        anew, haOuterNew, haSame, haNewA⟩ := hInnerFlip
      left
      refine ⟨m, d, hm, hInnerProper, V', New, hNew,
        hFiniteNew, flip, newOuter, hEHN, hCoords,
        hSymbol, hStrictB, hExterior, ?_⟩
      exact ⟨anew, haOuterNew,
        (by simpa only [hRight] using haSame), haNewA⟩

end AllThoseRamseyClasses.Lifts
