import AllThoseRamseyClasses.Lifts.Claim2ConditionalLargerGeometricPiece
import AllThoseRamseyClasses.Lifts.GeometricPieceCutRestriction
import AllThoseRamseyClasses.Lifts.GeometricProperSubpiece

/-!
# A genuine proper sub-piece from the two missing Claim 2 boundary inclusions

Let (P,R) be an actual geometric piece of a finite native functional
source, with its selected connected component C. Let S be a closed
cut containing R, and let x,y ∈ C \ S belong to DIFFERENT components
after deleting S.

Assume the central boundary conclusion sought by the printed Claim 2:
the old root R lies in the generated neighbourhood closures of BOTH
Source \ S components containing x and y.

The previously verified geometric localization proves that S ∩ P
is closed and that the x/y components after deleting S ∩ P are
EXACTLY their respective components after deleting S. Hence the
same two boundary inclusions hold for S ∩ P.

Select a minimal closed separator T INSIDE S ∩ P. The verified
boundary-closure lemma forces R ⊂ T strictly, since x and y remain
connected when only R is deleted. Enumerate T as the literal root
of a genuine new geometric piece Q. Its selected component is a
proper subset of C. Crucially, the WHOLE root of Q also lies in P,
so Q is an ACTUAL PROPER sub-piece of P in the paper's definition.

This establishes the entire conditional geometric sub-piece
production step and the strict finite vertex counts WITHOUT any
weak-image quotient or target-root injectivization.

It does NOT prove the two assumed boundary inclusions for the
chosen A',B' components of the printed minimal mixed piece. Nor
does it prove that Q is mixed or has an injective image root, or
construct the final alternative flip. These remain the genuine
mathematical obstacles to unrestricted Section 3 strong AP/Ramsey.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The exact *proper-subpiece* consequence of the still-open
two-boundary step of Claim 2, in the original native function
language. The selected new piece's FULL vertex set is strictly
contained in the old piece, with strictly fewer total vertices.

All extra assumptions explicitly concern the original forbidden
SOURCE, not the geometry of a substituted weak-image quotient. -/
theorem finite_geometricPiece_exists_properSubpiece_of_twoBoundaries
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hSclosed : A.IsClosed S)
    (hRootS : Set.range P.roots ⊆ S)
    (x y : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left)
    (hyOld : y.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left)
    (hSepS : ¬ ReachOutside A.graph S x y)
    (hBoundary :
      Set.range P.roots ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)) ∧
      Set.range P.roots ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S y))) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData A m),
      Set.range P.roots ⊂ Set.range Q.roots ∧
      Set.range Q.roots ⊆ S ∧
      geometricPieceVertices A Q ⊂ geometricPieceVertices A P ∧
      (geometricPieceVertices A Q).ncard <
        (geometricPieceVertices A P).ncard ∧
      (functionalComponentFrom A (Set.range Q.roots) Q.left).ncard <
        (functionalComponentFrom A (Set.range P.roots) P.left).ncard := by
  let T : Set V := S ∩ geometricPieceVertices A P
  have hTclosed : A.IsClosed T :=
    geometricPiece_intersectClosedCut_isClosed A P S hSclosed
  have hRootT : Set.range P.roots ⊆ T :=
    geometricPiece_root_subset_intersectCut A P S hRootS
  let hTS : T ⊆ S := Set.inter_subset_left
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  let yT : {v : V // v ∉ T} := outsideCutMap hTS y
  have hSepT : ¬ ReachOutside A.graph T xT yT :=
    geometricPiece_intersectCut_separates
      A P S hRootS x y hxOld hSepS
  have hxEq :
      componentFrom A.graph T xT = componentFrom A.graph S x :=
    geometricPiece_component_intersectCut_eq A P S hRootS x hxOld
  have hyEq :
      componentFrom A.graph T yT = componentFrom A.graph S y :=
    geometricPiece_component_intersectCut_eq A P S hRootS y hyOld
  have hBoundaryT :
      Set.range P.roots ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph T xT)) ∧
      Set.range P.roots ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph T yT)) := by
    constructor
    · simpa only [hxEq] using hBoundary.1
    · simpa only [hyEq] using hBoundary.2
  obtain ⟨m, Q, hStrictRoot, hQrootT,
      _hQleft, hQright, hCompProper, hCompCount⟩ :=
    finite_geometricPiece_strictComponentDescent_of_boundaries
      A P T hTclosed hRootT xT yT
      hxOld hyOld hSepT hBoundaryT
  have hQrootP :
      Set.range Q.roots ⊆ geometricPieceVertices A P :=
    hQrootT.trans Set.inter_subset_right
  have hRightOld :
      Q.right.1 ∈ functionalComponentFrom
        A (Set.range P.roots) P.left := by
    rw [hQright]
    exact hyOld
  have hProper :
      geometricPieceVertices A Q ⊂ geometricPieceVertices A P :=
    geometricPiece_proper_subpiece_of_rightInOldComponent
      A P Q hQrootP hCompProper.subset hRightOld
  have hTotalCount :
      (geometricPieceVertices A Q).ncard <
        (geometricPieceVertices A P).ncard :=
    Set.ncard_lt_ncard hProper
  have hQrootS : Set.range Q.roots ⊆ S :=
    hQrootT.trans Set.inter_subset_left
  exact ⟨m, Q, hStrictRoot, hQrootS,
    hProper, hTotalCount, hCompCount⟩

end AllThoseRamseyClasses.Lifts
