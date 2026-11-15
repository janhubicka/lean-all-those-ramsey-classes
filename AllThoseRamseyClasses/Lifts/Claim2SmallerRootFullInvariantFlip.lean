import AllThoseRamseyClasses.Lifts.RootRetentionLocalization
import AllThoseRamseyClasses.Lifts.Claim2SameWitnessGeometricStateStep
import AllThoseRamseyClasses.Lifts.Claim2NativeBActiveBoundaryBridge

/-!
# Track B: no old-root capture and no A-mixedness yield a full-invariant step

The original genuine smaller-root no-capture proof establishes exact
source component containment, proper nesting and A-free B-component
eligibility. Apply the full same-Q actual geometric flip to that SAME
proper nested piece, carrying original root-target injectivity and
piece-scoped B-active generated-boundary injection to the NEW source.

Native boundary conversion is supplied by the exact target
free-amalgam overlap theorem; no global source map injection.
The two smaller-root obstructions are premises, not eliminated.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Conditional no-capture/no-A-mixed smaller-root state transition,
preserving every iterative invariant on a single new native source. -/
theorem claim2_smallerRoot_noOldCapture_noA_hasFullInvariantFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m) (hn : 0 < n)
    (hNewRootInOldPiece :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hDleftInOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hDrightInOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hNoOldRootCapture :
      ∀ r : V, r ∈ Set.range P.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.left)
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
    (hInnerRootInSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoAInsideD : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hDrootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hDleftRight : d.left.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hDrightLeft : d.right.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hOldOuterRootTargetInj :
      Function.Injective (fun i : Fin n => f (P.roots i)))
    (hOldActiveBoundaryInj :
      ∀ (z : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        z.1 ∈ geometricPieceVertices Source P →
        z.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) z)))) :
    geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P ∧
      ∃ (V' : Type) (New : Structure L V') (hNew : F New)
        (hFiniteNew : Finite V') (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin n, flip (newOuter.roots i) = f (P.roots i)) ∧
        geometricGlobalPieceSymbol F Source hFinite hForbidden P hn =
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
        ∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f d.right.1 ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft ∧
        Function.Injective (fun i : Fin n => flip (newOuter.roots i)) ∧
        (∀ (z : {w : V' //
            w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
          z.1 ∈ geometricPieceVertices New newOuter →
          z.1 ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
          Set.InjOn flip
            (New.functionClosure
              (gaifmanNeighborhood New.graph
                (componentFrom New.graph
                  (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) z)))) := by
  classical
  have hDcomponentInsideP :
      functionalComponentFrom Source
        (Set.range d.roots) d.left ⊆
      functionalComponentFrom Source
        (Set.range P.roots) P.left := by
    by_contra hEscape
    obtain ⟨r, hrOldRoot, hrCaptured⟩ :=
      geometricPiece_escapingComponent_capturesOldRoot
        Source P d hDleftInOld hEscape
    exact hNoOldRootCapture r hrOldRoot hrCaptured
  have hInnerInside :
      geometricPieceVertices Source d ⊆
      geometricPieceVertices Source P := by
    intro z hz
    rcases hz with hRoot | hComp
    · exact hNewRootInOldPiece hRoot
    · exact Or.inr (hDcomponentInsideP hComp)
  have hRightNotInD :
      d.right.1 ∉ geometricPieceVertices Source d := by
    intro hz
    rcases hz with hR | hC
    · exact d.right.2 hR
    · have hRSubtype :
          (⟨d.right.1, hC.1⟩ :
            {z : V // z ∉ Set.range d.roots}) = d.right :=
          Subtype.ext rfl
      exact d.minimal.2.1
        (by simpa only [hRSubtype] using hC.2)
  have hProper :
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hInnerInside, ?_⟩
    intro hEqual
    have hRightOld :
        d.right.1 ∈ geometricPieceVertices Source P :=
      Or.inr hDrightInOld
    exact hRightNotInD (hEqual.symm ▸ hRightOld)
  have hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Source
        (Set.range d.roots) d.left := by
    intro i
    exact hNoOldRootCapture (P.roots i) ⟨i, rfl⟩
  have hxD : d.left.1 ∈ functionalComponentFrom Source
      (Set.range d.roots) d.left :=
    componentFrom_root Source.graph (Set.range d.roots) d.left
  have hAnchorA :
      f d.right.1 ∈ fullFreeLeftExclusiveTarget iLeft jLeft :=
    (weakFreeLeftPart_iff_targetExclusive
      iLeft jLeft f d.right.1).mp hDrightLeft
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      hFiniteNew, flip, newOuter,
      hFlip, hQNoB, hEAgree, hCarrier, hCoords, hSymbol,
      hStrictB, hExterior, anew, haOuter, haImage, haLeft,
      hNewRootInj, hNewTargetBoundaryInj⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorRootAndBoundaryInj
      F hFiniteF Source hFinite hForbidden
      P d hm hn hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRootInSeam hNoAInsideD hDrootTargetInjective
      d.left.1 hxD hDleftRight
      d.right.1 (Or.inr hDrightInOld) hAnchorA
      hOldOuterRootTargetInj hOldActiveBoundaryInj
  have hNewNativeBoundaryInj :
      ∀ (z : {w : V' //
          w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
        z.1 ∈ geometricPieceVertices New newOuter →
        z.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) z))) :=
    claim2_fullRightActiveBoundary_to_weakRightActiveBoundary
      New newOuter Target flip X Left Right jLeft jRight
      iLeft iRight hFree hNewTargetBoundaryInj
  exact ⟨hProper, V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hCoords, hSymbol, hStrictB, hExterior,
    anew, haOuter, haImage, haLeft, hNewRootInj, hNewNativeBoundaryInj⟩

end AllThoseRamseyClasses.Lifts
