import AllThoseRamseyClasses.Lifts.GeometricPieceCutRestriction
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Select a real auxiliary minimal closed separator INSIDE the old piece

Let P=(R,C) be a genuine old geometric functional source piece,
and let S be any larger FUNCTION-CLOSED cut containing R.

For two vertices x,y of C outside S that are disconnected after
deleting S, the whole intersection T=S∩(R∪C) is function-closed
and still separates x,y. These two assertions were independently
checked in GeometricPieceCutRestriction.

For a finite source the certified minimal-closed-separator
selection produces U ⊆ T. Enumerating the full cut U yields an
ACTUAL geometric source piece Q with both distinguished vertices
exactly x,y and WHOLE root U contained in the old piece.
When x,y are joined by an empty-cut source path, U has positive
width, as required by the original Section 3 global canonical lift.

This disposes of the "the auxiliary separator might go outside
the old piece" issue for the literal existence/selection step.
It does NOT ensure that the new component captures an old-root
vertex, nor establish a proper B-only flip, preservation of the
outer context or unrestricted strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every pair of vertices from the old selected component,
separated by a larger closed common-root cut S, can be separated
by a GENUINE inclusion-minimal function-closed cut U wholly inside
S intersected with the old piece. The roots of the resulting
geometric chart are distinct SOURCE vertices, with no claim about
injectivity of their target EHN images. -/
theorem finite_geometricPiece_selectInteriorMinimalClosedSeparator
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V) (hSclosed : A.IsClosed S)
    (hRS : Set.range P.roots ⊆ S)
    (x y : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left)
    (hSepS : ¬ ReachOutside A.graph S x y) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData A m),
      Set.range Q.roots ⊆
        S ∩ geometricPieceVertices A P ∧
      Q.left.1 = x.1 ∧ Q.right.1 = y.1 := by
  let T : Set V := S ∩ geometricPieceVertices A P
  have hTclosed : A.IsClosed T :=
    geometricPiece_intersectClosedCut_isClosed A P S hSclosed
  let hTS : T ⊆ S := Set.inter_subset_left
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  let yT : {v : V // v ∉ T} := outsideCutMap hTS y
  have hSepT : ¬ ReachOutside A.graph T xT yT :=
    geometricPiece_intersectCut_separates
      A P S hRS x y hxOld hSepS
  obtain ⟨U, hUT, hMinimal⟩ :=
    finite_exists_minimalClosedSeparator_inside
      A T hTclosed xT yT hSepT
  obtain ⟨m, Q, hRootU, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart
      A U (outsideCutMap hUT xT)
          (outsideCutMap hUT yT) hMinimal
  refine ⟨m, Q, ?_, hLeft, hRight⟩
  rw [hRootU]
  exact hUT

/-- If the separated vertices x,y have an actual empty-cut
Gaifman path in the original source, the chosen auxiliary
interior root is necessarily NONEMPTY. This selects the
positive-width original-global piece without any target-map
injectivity or all-test profile assumptions. -/
theorem finite_geometricPiece_selectPositiveInteriorCut
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V) (hSclosed : A.IsClosed S)
    (hRS : Set.range P.roots ⊆ S)
    (x y : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left)
    (hSepS : ¬ ReachOutside A.graph S x y)
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨y.1, by simp⟩ : {v : V // v ∉ ∅})) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData A m),
      0 < m ∧
      Set.range Q.roots ⊆
        S ∩ geometricPieceVertices A P ∧
      Q.left.1 = x.1 ∧ Q.right.1 = y.1 := by
  obtain ⟨m, Q, hQroot, hQL, hQR⟩ :=
    finite_geometricPiece_selectInteriorMinimalClosedSeparator
      A P S hSclosed hRS x y hxOld hSepS
  have hQpath : ReachOutside A.graph (∅ : Set V)
      (⟨Q.left.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨Q.right.1, by simp⟩ : {v : V // v ∉ ∅}) := by
    simpa only [hQL, hQR] using hConnected
  exact ⟨m, Q,
    geometricPiece_positiveWidth_of_emptyCut_path A Q hQpath,
    hQroot, hQL, hQR⟩

end AllThoseRamseyClasses.Lifts
