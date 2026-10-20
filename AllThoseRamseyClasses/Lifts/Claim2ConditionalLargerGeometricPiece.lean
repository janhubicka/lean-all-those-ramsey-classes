import AllThoseRamseyClasses.Lifts.ClosedBoundaryIntersectionCut
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart
import Mathlib.Data.Set.Card

/-!
# Actual larger minimal closed separator inside a mixed forbidden piece

This isolates the final cut-selection step in the printed Section 3
Claim 2, using only the source's actual function-closed sets.

Let S be a closed separator of two vertices x,y, and let R₀ ⊆ S
be a previously selected piece root. Assume:
* x,y are STILL connected after deleting R₀;
* R₀ lies in the function-closures of the neighbourhoods of BOTH
  components of Source \ S containing x,y.

Choose a minimal function-closed separator C ⊆ S between x,y.
The independently verified two-boundary transport theorem gives
R₀ ⊆ C. Since R₀ does not separate x,y, this containment is
STRICT. Enumerate C to obtain a GENUINE geometric piece with
full native function data, and show that its selected nonroot
component is properly smaller than the component of the old piece.

For the original 2019 Claim 2, the two-boundary assumption is the
substantive as-yet-unproved step concerning the selected A',B'.
Also, a larger root C can contain vertices outside the old piece;
strict component decrease does not alone certify a PROPER sub-piece
or make its weak image flippable. Neither is asserted here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Under the TWO explicit boundary-closure inclusions, a finite
closed cut S contains a minimal closed separator C of x and y
which strictly contains the old root R₀ when R₀ does not
already separate the chosen vertices.

The new C is an ACTUAL source function-closed set; it is not the
closure of a guessed vertex cut. -/
theorem finite_exists_strictlyLargerMinimalClosedSeparator
    [Finite V]
    (A : Structure L V) (S R₀ : Set V)
    (hSclosed : A.IsClosed S)
    (hR₀S : R₀ ⊆ S)
    (x y : {v : V // v ∉ S})
    (hSepS : ¬ ReachOutside A.graph S x y)
    (hReachR₀ : ReachOutside A.graph R₀
      (outsideCutMap hR₀S x) (outsideCutMap hR₀S y))
    (hBoundary :
      R₀ ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)) ∧
      R₀ ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S y))) :
    ∃ (C : Set V) (hCS : C ⊆ S),
      IsMinimalClosedSeparator A C
        (outsideCutMap hCS x) (outsideCutMap hCS y) ∧
      R₀ ⊂ C := by
  obtain ⟨C, hCS, hMin⟩ :=
    finite_exists_minimalClosedSeparator_inside
      A S hSclosed x y hSepS
  have hR₀C : R₀ ⊆ C :=
    rootedBoundarySubset_of_smallerClosedSeparator
      A hMin.1 hCS x y hMin.2.1 hBoundary
  have hR₀neC : R₀ ≠ C := by
    intro hEq
    subst R₀
    have hPathC : ReachOutside A.graph C
        (outsideCutMap hCS x) (outsideCutMap hCS y) := by
      simpa only [outsideCutMap] using hReachR₀
    exact hMin.2.1 hPathC
  exact ⟨C, hCS, hMin,
    Set.ssubset_iff_subset_ne.mpr ⟨hR₀C, hR₀neC⟩⟩

/-- For an ACTUAL old geometric piece whose two selected source
vertices x,y lie in the same old selected component, an
intermediate separating closed cut S and the two boundary
hypotheses give a NEW genuine geometric piece.

Its root strictly extends the old root; its left component is
a PROPER subset of the old selected nonroot component, hence has
strictly fewer vertices for finite sources. This does not
silently promote it to a proper sub-piece: its new root may
contain vertices outside the original piece. -/
theorem finite_geometricPiece_strictComponentDescent_of_boundaries
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hSclosed : A.IsClosed S)
    (hOldS : Set.range d.roots ⊆ S)
    (x y : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range d.roots) d.left)
    (hyOld : y.1 ∈ functionalComponentFrom
      A (Set.range d.roots) d.left)
    (hSepS : ¬ ReachOutside A.graph S x y)
    (hBoundary :
      Set.range d.roots ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)) ∧
      Set.range d.roots ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S y))) :
    ∃ (m : ℕ) (e : GeometricFunctionalPieceData A m),
      Set.range d.roots ⊂ Set.range e.roots ∧
      Set.range e.roots ⊆ S ∧
      e.left.1 = x.1 ∧ e.right.1 = y.1 ∧
      functionalComponentFrom A (Set.range e.roots) e.left ⊂
        functionalComponentFrom A (Set.range d.roots) d.left ∧
      (functionalComponentFrom A (Set.range e.roots) e.left).ncard <
        (functionalComponentFrom A (Set.range d.roots) d.left).ncard := by
  have hPathX : ReachOutside A.graph (Set.range d.roots)
      d.left (outsideCutMap hOldS x) := hxOld.2
  have hPathY : ReachOutside A.graph (Set.range d.roots)
      d.left (outsideCutMap hOldS y) := hyOld.2
  have hPathOld : ReachOutside A.graph (Set.range d.roots)
      (outsideCutMap hOldS x) (outsideCutMap hOldS y) :=
    (reachOutside_symm A.graph (Set.range d.roots) hPathX).trans hPathY
  obtain ⟨C, hCS, hMin, hOldC⟩ :=
    finite_exists_strictlyLargerMinimalClosedSeparator
      A S (Set.range d.roots) hSclosed hOldS
      x y hSepS hPathOld hBoundary
  obtain ⟨m, e, hRootC, hLeftX, hRightY⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart A C
      (outsideCutMap hCS x) (outsideCutMap hCS y) hMin
  have hOldNew : Set.range d.roots ⊂ Set.range e.roots := by
    simpa only [hRootC] using hOldC
  have hNewS : Set.range e.roots ⊆ S := by
    simpa only [hRootC] using hCS
  have hOldNewSubset : Set.range d.roots ⊆ Set.range e.roots :=
    hOldNew.subset
  have hNewLeftOld :
      outsideCutMap hOldNewSubset e.left = outsideCutMap hOldS x := by
    apply Subtype.ext
    exact hLeftX
  have hCompSubset :
      functionalComponentFrom A (Set.range e.roots) e.left ⊆
      functionalComponentFrom A (Set.range d.roots) d.left := by
    intro z hzNew
    have hzOld :=
      componentFrom_subset_of_cut_subset
        A.graph hOldNewSubset e.left hzNew
    have hPathXZ : ReachOutside A.graph (Set.range d.roots)
        (outsideCutMap hOldS x) ⟨z, hzOld.1⟩ := by
      simpa only [hNewLeftOld] using hzOld.2
    exact ⟨hzOld.1, hPathX.trans hPathXZ⟩
  have hyNotNew :
      y.1 ∉ functionalComponentFrom A (Set.range e.roots) e.left := by
    intro hyNew
    have hYeq :
        (⟨y.1, hyNew.1⟩ : {v : V // v ∉ Set.range e.roots}) =
        e.right := by
      apply Subtype.ext
      exact hRightY.symm
    have hPathE : ReachOutside A.graph (Set.range e.roots)
        e.left e.right := by
      simpa only [hYeq] using hyNew.2
    exact e.minimal.2.1 hPathE
  have hProper :
      functionalComponentFrom A (Set.range e.roots) e.left ⊂
        functionalComponentFrom A (Set.range d.roots) d.left := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hCompSubset, ?_⟩
    intro hEq
    apply hyNotNew
    rw [hEq]
    exact hyOld
  refine ⟨m, e, hOldNew, hNewS, hLeftX, hRightY, hProper, ?_⟩
  exact Set.ncard_lt_ncard hProper

end AllThoseRamseyClasses.Lifts
