import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import Mathlib.Data.Set.Card

/-!
# Proper geometric sub-pieces in the sense of the 2019 manuscript

A source-attached geometric piece is its full closed root R together
with ONE connected component C of the source outside R. A second
genuine geometric piece Q is a sub-piece of P exactly when its WHOLE
vertex set, including its function-closed root, is contained in P.

If Q's root is in P, Q's selected nonroot component is contained
in the nonroot component of P, and Q's opposite distinguished
vertex lies in P's old nonroot component, then Q is actually a
PROPER sub-piece of P: the distinguished opposite vertex belongs
to P but neither to Q's root nor to Q's selected component.

This is an exact statement about actual finite or infinite native
functional piece structures, not merely an inequality of nonroot
component sizes. No homomorphism-embedding, forbidden-family
membership, maximal trace or proposed flip is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Precisely the paper's strict sub-piece criterion for actual
native geometric pieces of the same source. The inclusion covers
ALL root vertices, not merely the selected nonroot component. -/
theorem geometricPiece_proper_subpiece_of_rightInOldComponent
    (A : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData A n)
    (Q : GeometricFunctionalPieceData A m)
    (hQroot :
      Set.range Q.roots ⊆ geometricPieceVertices A P)
    (hQcomponent :
      functionalComponentFrom A (Set.range Q.roots) Q.left ⊆
        functionalComponentFrom A (Set.range P.roots) P.left)
    (hQright :
      Q.right.1 ∈ functionalComponentFrom
        A (Set.range P.roots) P.left) :
    geometricPieceVertices A Q ⊂ geometricPieceVertices A P := by
  have hSubset :
      geometricPieceVertices A Q ⊆ geometricPieceVertices A P := by
    intro z hz
    rcases hz with hzRoot | hzComp
    · exact hQroot hzRoot
    · exact Or.inr (hQcomponent hzComp)
  have hRightNotInQ :
      Q.right.1 ∉ geometricPieceVertices A Q := by
    intro h
    rcases h with hRoot | hComp
    · exact Q.right.2 hRoot
    · exact Q.minimal.2.1 hComp.2
  have hRightInP :
      Q.right.1 ∈ geometricPieceVertices A P :=
    Or.inr hQright
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hSubset, ?_⟩
  intro hEq
  exact hRightNotInQ (by
    rw [hEq]
    exact hRightInP)

/-- For a FINITE source, a genuine proper sub-piece has strictly
fewer TOTAL vertices, including the roots. The published Claim 2
also compares nonroot component sizes separately; neither count
should be silently identified with the other. -/
theorem geometricPiece_proper_subpiece_strictTotalCount
    [Finite V]
    (A : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData A n)
    (Q : GeometricFunctionalPieceData A m)
    (hQroot :
      Set.range Q.roots ⊆ geometricPieceVertices A P)
    (hQcomponent :
      functionalComponentFrom A (Set.range Q.roots) Q.left ⊆
        functionalComponentFrom A (Set.range P.roots) P.left)
    (hQright :
      Q.right.1 ∈ functionalComponentFrom
        A (Set.range P.roots) P.left) :
    (geometricPieceVertices A Q).ncard <
      (geometricPieceVertices A P).ncard := by
  exact Set.ncard_lt_ncard
    (geometricPiece_proper_subpiece_of_rightInOldComponent
      A P Q hQroot hQcomponent hQright)

end AllThoseRamseyClasses.Lifts
