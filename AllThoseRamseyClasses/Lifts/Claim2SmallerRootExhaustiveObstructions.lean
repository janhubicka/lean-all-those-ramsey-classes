import AllThoseRamseyClasses.Lifts.Claim2SmallerRootNoCaptureGeometricFlip

/-!
# Exhaustive smaller-root obstruction alternatives

A genuine smaller positive closed-separator root inside the old outer
geometric piece can fail eligibility for an inner selected-Q flip
in exactly two visible ways: its chosen source component captures
some old outer root vertex, or its component is A-mixed.
Absent BOTH conditions, the already verified conditional actual
source flip applies. This theorem records the exhaustive choice.
It does not eliminate the first two branches or claim that the
published 2019 strong amalgamation argument is complete.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Either old-root capture, A-mixedness, or a genuine B-to-A flip
of the selected smaller-root piece, preserving the full old global
symbol and exterior SOURCE counts with a surviving A-only anchor. -/
theorem claim2_smallerRoot_capture_or_mixed_or_actualGeometricFlip
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
    (hDrootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hDleftRight : d.left.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hDrightLeft : d.right.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f) :
    (∃ r : V, r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source (Set.range d.roots) d.left) ∨
    (∃ z : V, z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left ∧
      z ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f) ∨
    (geometricPieceVertices Source d ⊂
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
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft) := by
  classical
  by_cases hCapture :
      ∃ r : V, r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left
  · exact Or.inl hCapture
  · have hNoOldRootCapture :
        ∀ r : V, r ∈ Set.range P.roots →
          r ∉ functionalComponentFrom Source
            (Set.range d.roots) d.left := by
      intro r hrRoot hrComp
      exact hCapture ⟨r, hrRoot, hrComp⟩
    by_cases hMixed :
        ∃ z : V,
          z ∈ functionalComponentFrom Source
            (Set.range d.roots) d.left ∧
          z ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f
    · exact Or.inr (Or.inl hMixed)
    · have hNoAInsideD : ∀ z : V,
          z ∈ functionalComponentFrom Source
            (Set.range d.roots) d.left →
          z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f := by
        intro z hzComp hzA
        exact hMixed ⟨z, hzComp, hzA⟩
      exact Or.inr (Or.inr
        (claim2_smallerRoot_noOldCapture_noA_hasActualGeometricFlip
          F hFiniteF Source hFinite hForbidden
          P d hm hn hNewRootInOldPiece
          hDleftInOld hDrightInOld hNoOldRootCapture
          Target f hf Left Right jLeft jRight
          X iLeft iRight hFree hCommon
          hInnerRootInSeam hNoAInsideD hDrootTargetInjective
          hDleftRight hDrightLeft))

end AllThoseRamseyClasses.Lifts
