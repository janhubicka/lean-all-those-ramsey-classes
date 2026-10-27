import AllThoseRamseyClasses.Lifts.RootRetentionLocalization
import Mathlib.Tactic

/-!
# The exact genuine split-old-root obstruction in general Claim 2

The source-only singleton-old-root result is based on a graph
obstruction that has a precise arbitrary-width formulation.

Let P be an old genuine geometric source piece, and Q another
genuine minimal closed-separator piece whose two distinguished
vertices both lie in P's selected old component. Suppose Q's
LEFT selected component captures some OLD root vertex of P.
If Q's OPPOSITE RIGHT component escapes P's selected old
component, the already checked escaping-component theorem
forces it to capture a SECOND old root vertex. Disjointness of
Q's two selected components forces the two root vertices
to be DISTINCT.

Thus the only genuine source geometry preventing localization
of Q's opposite B-component is a literal SPLIT of the old
separator root across distinct components of Source minus Q's
new root. In particular the old root must have width at least 2.

This rules out the split in the verified singleton-root case,
and isolates the actual new multi-root difficulty, without
assuming that root splitting never happens. The proof uses
native Gaifman components and FULL source separator pieces;
there is no weak target-map quotient, injection or forbidden
family hypothesis in these lemmas.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- If the opposite component of Q escapes the old selected
component of P, while Q's left component already contains an
old root point, then the two components split TWO DISTINCT
source vertices of P's old root. -/
theorem geometricPiece_escapingOpposite_splitsOldRoot
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hCapturedLeft :
      ∃ r : V,
        r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.left)
    (hRightEscapes :
      ¬ functionalComponentFrom Source
          (Set.range Q.roots) Q.right ⊆
        functionalComponentFrom Source
          (Set.range P.roots) P.left) :
    ∃ rL rR : V,
      rL ≠ rR ∧
      rL ∈ Set.range P.roots ∧
      rR ∈ Set.range P.roots ∧
      rL ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left ∧
      rR ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.right := by
  let Qswap : GeometricFunctionalPieceData Source m := {
    roots := Q.roots
    roots_injective := Q.roots_injective
    left := Q.right
    right := Q.left
    minimal := minimalClosedSeparator_swap
      Source (Set.range Q.roots) Q.left Q.right Q.minimal
  }
  obtain ⟨rL, hrLOld, hrLLeft⟩ := hCapturedLeft
  obtain ⟨rR, hrROld, hrRRight⟩ :=
    geometricPiece_escapingComponent_capturesOldRoot
      Source P Qswap hQrightOld hRightEscapes
  have hne : rL ≠ rR := by
    intro hEq
    have hrLRight :
        rL ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right := by
      simpa only [hEq] using hrRRight
    exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint Source Q))
      hrLLeft hrLRight
  exact ⟨rL, rR, hne, hrLOld, hrROld, hrLLeft, hrRRight⟩

/-- A genuine escaping opposite component necessarily witnesses
old geometric root WIDTH AT LEAST TWO. This is the precise
obstruction not present in the complete singleton-root proof. -/
theorem geometricPiece_escapingOpposite_forcesOldRootWidthTwo
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hCapturedLeft :
      ∃ r : V,
        r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.left)
    (hRightEscapes :
      ¬ functionalComponentFrom Source
          (Set.range Q.roots) Q.right ⊆
        functionalComponentFrom Source
          (Set.range P.roots) P.left) :
    2 ≤ n := by
  obtain ⟨rL, rR, hne, hrLOld, hrROld, _, _⟩ :=
    geometricPiece_escapingOpposite_splitsOldRoot
      Source P Q hQrightOld hCapturedLeft hRightEscapes
  obtain ⟨i, hi⟩ := hrLOld
  obtain ⟨j, hj⟩ := hrROld
  have hij : i ≠ j := by
    intro hEq
    apply hne
    calc
      rL = P.roots i := hi.symm
      _ = P.roots j := congrArg P.roots hEq
      _ = rR := hj
  have hv : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  have hiBound : i.val < n := i.isLt
  have hjBound : j.val < n := j.isLt
  omega

/-- If no two different old separator-root vertices can be
captured on opposite sides of Q, the opposite selected
component remains inside the old component. This is
the precise root-locality criterion needed before applying
mixed-piece minimality and the original B-to-A flip. -/
theorem geometricPiece_oppositeComponent_localized_of_noOldRootSplit
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hCapturedLeft :
      ∃ r : V,
        r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.left)
    (hNoSplit :
      ¬ ∃ rL rR : V,
        rL ≠ rR ∧
        rL ∈ Set.range P.roots ∧
        rR ∈ Set.range P.roots ∧
        rL ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.left ∧
        rR ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right) :
    functionalComponentFrom Source
      (Set.range Q.roots) Q.right ⊆
      functionalComponentFrom Source
        (Set.range P.roots) P.left := by
  by_contra hEscape
  exact hNoSplit (geometricPiece_escapingOpposite_splitsOldRoot
    Source P Q hQrightOld hCapturedLeft hEscape)

end AllThoseRamseyClasses.Lifts
