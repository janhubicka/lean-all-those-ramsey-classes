import AllThoseRamseyClasses.Lifts.ExactOppositeBoundarySeparator
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Exact-root geometric source piece from an uncovered opposite boundary

Suppose a native closed separator T splits two source vertices x,y
and is exactly the COMPLETE generated boundary of the x-component
of Source minus T. Define the opposite generated boundary
U = Cl(N(component(Source minus T,y))). The verified source
boundary-intersection lemma now proves that U ITSELF is a
minimal closed separator: no extra finite min-cut minimization.

For finite sources, enumerate exactly the vertices of U as
the ordered distinct roots of a GENUINE geometric piece, with
the SAME original source vertices y and x distinguished on
opposite sides. If coverage T⊆U fails, U⊊T. If those vertices
are connected in the full original source, the width is positive.

Compared with the earlier #611 construction, the output now
specifies the FULL root EQUALITY, not merely inclusion in T.
This sharpens the old-root capture obstruction in Claim 2.
It does not prove a new piece lies in an old piece or that
any weak target root tuple is injective.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The opposite generated boundary U is the EXACT root of a
positive-width genuine geometric source piece. Failure of
coverage makes this exact root a STRICT subset of the old
closed separator T. Source vertices are preserved literally. -/
theorem finite_uncoveredBoundary_hasExactOppositeRootGeometricPiece
    [Finite V]
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x y : {z : V // z ∉ T})
    (hSepT : ¬ ReachOutside A.graph T x y)
    (hFullXBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T x)) = T)
    (hUncovered : ¬ T ⊆
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)))
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData A n),
      0 < n ∧
      Set.range d.roots = A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)) ∧
      Set.range d.roots ⊂ T ∧
      d.left.1 = y.1 ∧ d.right.1 = x.1 := by
  let U : Set V :=
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  let hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut A T hTclosed y
  have hProper : U ⊂ T := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hUT, ?_⟩
    intro hEq
    apply hUncovered
    intro z hz
    change z ∈ U
    rw [hEq]
    exact hz
  have hMinUxy :
      IsMinimalClosedSeparator A U
        (outsideCutMap hUT x) (outsideCutMap hUT y) :=
    oppositeBoundaryClosure_isMinimalClosedSeparator
      A T hTclosed x y hSepT hFullXBoundary
  have hMinUyx :
      IsMinimalClosedSeparator A U
        (outsideCutMap hUT y) (outsideCutMap hUT x) :=
    minimalClosedSeparator_swap A U
      (outsideCutMap hUT x) (outsideCutMap hUT y) hMinUxy
  obtain ⟨n, d, hRoot, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart A U
      (outsideCutMap hUT y) (outsideCutMap hUT x) hMinUyx
  have hPathD : ReachOutside A.graph (∅ : Set V)
      (⟨d.left.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    rw [hLeft, hRight]
    exact reachOutside_symm A.graph (∅ : Set V) hConnected
  have hn : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path A d hPathD
  have hRootProper : Set.range d.roots ⊂ T := by
    rw [hRoot]
    exact hProper
  exact ⟨n, d, hn, hRoot, hRootProper, hLeft, hRight⟩

end AllThoseRamseyClasses.Lifts
