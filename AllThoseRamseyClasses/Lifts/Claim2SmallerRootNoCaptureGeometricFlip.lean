import AllThoseRamseyClasses.Lifts.RootRetentionLocalization
import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStepAnchor

/-!
# A smaller-root alternative yields a real B-to-A flip if it does not capture old roots

The unresolved positive-rank local Claim 2 dichotomy can return a
genuine smaller positive minimal closed separator piece d whose
left distinguished vertex is B-exclusive and right vertex A-exclusive.
Its root lies inside the original outer geometric piece P, but its
selected component can capture an old P-root vertex or become mixed.
This prevents directly treating d as a proper B-only inner piece.

Here is a precise CONDITIONAL source-level repair of one branch:

1. If the selected d-component captures NO vertex of the complete
   old P separating root, the already verified escaping-component
   source lemma forces that component to stay INSIDE P's component.
2. Since d's full root lies in P, d is then an ACTUAL PROPER
   subpiece of P: d.right is in the old component but outside
   d's selected component by genuine minimal separation.
3. If d's selected component is A-free and its full root has
   injective target images in the common seam, the verified
   same-selected-Q native B-to-A source flip applies to d
   inside P. It strictly decreases B-only SOURCE rank inside
   one new actual outer geometric piece, conserves all exterior
   source counts, preserves the old outer target-root coordinates
   and global canonical symbol, and retains the A-only source
   anchor d.right itself.

This theorem uses no globally minimal A-support witness, and no
smallest-mixed-piece assumption. The remaining smaller-root
obstructions are EXACTLY old-root capture and A-mixedness of
the selected d-component. Neither is assumed impossible.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine smaller positive-root piece has an actual proper
geometric B-only source flip inside the old piece, provided
its B-originating component captures no OLD outer-root vertex
and remains A-free. The right distinguished vertex supplies
the surviving A-only SOURCE anchor.

No global weak-map seam injectivity or original minimizer
is assumed; only the selected d-root target coordinates
must be injected, as required by the canonical flip. -/
theorem claim2_smallerRoot_noOldCapture_noA_hasActualGeometricFlip
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
      (sL := iLeft) (iL := jLeft) f) :
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
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
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
  obtain ⟨V', New, hNew, hFiniteNew, flip, newOuter,
      hFlip, hCoords, hSymbol, hStrictB, hExterior,
      anew, haOuter, haImage, haLeft⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withExteriorAndAnchor
      F hFiniteF Source hFinite hForbidden
      P d hm hn hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRootInSeam hNoAInsideD hDrootTargetInjective
      d.left.1 hxD hDleftRight
      d.right.1 (Or.inr hDrightInOld) hAnchorA
  exact ⟨hProper, V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hCoords, hSymbol, hStrictB, hExterior,
    anew, haOuter, haImage, haLeft⟩

end AllThoseRamseyClasses.Lifts
