import AllThoseRamseyClasses.Lifts.MinimalSeparatorReverse

/-!
# The intersection of two component-boundary closures lies in each smaller cut

The 2019 Section 3 Claim 2 proof uses the following implication:
if R is a cut with two selected components, and a smaller CLOSED
separator S ⊆ R still separates those components, then any vertex
belonging to the generated closures of BOTH old component
neighbourhoods must already lie in S.

This is not automatic from ordinary neighborhood containment:
function closure can add vertices that have no edge to the component.
The verified boundary-closure transport lemma handles these generated
vertices. After transport each common vertex outside S would belong
to BOTH disjoint components of Source \ S, a contradiction.

The result is precisely the set-theoretic tool for the manuscript's
inclusion R' ⊆ C once the additional boundary incidences required by
Claim 2 have been proved. Neither those incidences nor the existence
of the final proper forbidden sub-piece is asserted here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A pair of components of a larger cut R has no common point
in the closures of their external Gaifman neighborhoods outside
a CLOSED smaller cut S ⊆ R that still separates their roots.

The conclusion holds for the actual generated native functional
closure, without assuming the larger cut is closed, and without any
finiteness or bound on the language's function arities. -/
theorem boundaryClosures_intersection_subset_smallerSeparator
    (A : Structure L V)
    {R S : Set V}
    (hSclosed : A.IsClosed S) (hSR : S ⊆ R)
    (x y : {v : V // v ∉ R})
    (hSeparate : ¬ ReachOutside A.graph S
      (outsideCutMap hSR x) (outsideCutMap hSR y)) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) ∩
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R y)) ⊆ S := by
  intro z hz
  rcases hz with ⟨hzX, hzY⟩
  by_cases hzS : z ∈ S
  · exact hzS
  have hzX' :
      z ∈ componentFrom A.graph S (outsideCutMap hSR x) := by
    have hx :=
      boundaryClosure_subset_smallerCutComponent A hSclosed hSR x hzX
    exact hx.resolve_left hzS
  have hzY' :
      z ∈ componentFrom A.graph S (outsideCutMap hSR y) := by
    have hy :=
      boundaryClosure_subset_smallerCutComponent A hSclosed hSR y hzY
    exact hy.resolve_left hzS
  have hDisjoint :
      Disjoint
        (componentFrom A.graph S (outsideCutMap hSR x))
        (componentFrom A.graph S (outsideCutMap hSR y)) :=
    componentFrom_disjoint_of_not_reach
      A.graph S (outsideCutMap hSR x) (outsideCutMap hSR y)
      hSeparate
  exact False.elim ((Set.disjoint_left.mp hDisjoint) hzX' hzY')

/-- A proposed root T lying in BOTH generated component-boundary
closures is contained in every smaller closed separator S of those
components. The hypotheses explicitly distinguish the actual old
component boundary certificates from the desired new separator. -/
theorem rootedBoundarySubset_of_smallerClosedSeparator
    (A : Structure L V)
    {R S T : Set V}
    (hSclosed : A.IsClosed S) (hSR : S ⊆ R)
    (x y : {v : V // v ∉ R})
    (hSeparate : ¬ ReachOutside A.graph S
      (outsideCutMap hSR x) (outsideCutMap hSR y))
    (hBoundary :
      T ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) ∧
      T ⊆ A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph R y))) :
    T ⊆ S := by
  intro z hzT
  apply boundaryClosures_intersection_subset_smallerSeparator
    A hSclosed hSR x y hSeparate
  exact ⟨hBoundary.1 hzT, hBoundary.2 hzT⟩

end AllThoseRamseyClasses.Lifts
