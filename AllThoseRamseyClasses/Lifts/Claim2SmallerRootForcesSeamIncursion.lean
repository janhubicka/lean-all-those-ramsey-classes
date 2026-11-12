import AllThoseRamseyClasses.Lifts.ExactOppositeBoundarySeparator
import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# Strictly smaller opposite root forces an actual source seam incursion

Let T be a function-closed cut separating actual native source
vertices x,y and be exactly the full generated external
neighbourhood boundary of the x-component. Let U be the
opposite y-component's full generated boundary. The already
verified source theorem makes U a minimal closed separator
contained in T.

If U is a PROPER subset of T, then the component of x after
deleting U must contain a SOURCE vertex of T outside U.

Otherwise every U-avoiding path out of the original x-component
would avoid T as well, giving equality of the old and new
x-components. Their complete function-generated boundaries
would then coincide. But minimality of U gives boundary U,
while the old boundary is T; a contradiction.

This is independent of forbidden-source minimality, finiteness,
EHN weak target-image injectivity and the target amalgam. It
works on the actual complete functional Gaifman graph. In
Claim 2, T lies inside the full shared-target seam preimage,
so the smaller-root branch always has a literal source-seam
vertex internal to the new x-side component.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Proper shrinking of the opposite generated separator
necessarily makes the x-side component swallow a vertex
from the old closed cut T, outside the smaller cut U. -/
theorem strictOppositeGeneratedBoundary_forces_xSideSeamIncursion
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x y : {z : V // z ∉ T})
    (hSeparated : ¬ ReachOutside A.graph T x y)
    (hExactX : A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T x)) = T)
    (hProper : A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T y)) ⊂ T) :
    ∃ z : V,
      z ∈ T ∧
      z ∉ A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)) ∧
      z ∈ componentFrom A.graph
        (A.functionClosure
          (gaifmanNeighborhood A.graph
            (componentFrom A.graph T y)))
        (outsideCutMap
          (functionalClosure_neighborhood_subset_cut
            A T hTclosed y) x) := by
  classical
  let U : Set V := A.functionClosure
    (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  have hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut A T hTclosed y
  let xU : {z : V // z ∉ U} := outsideCutMap hUT x
  let yU : {z : V // z ∉ U} := outsideCutMap hUT y
  let C : Set V := componentFrom A.graph T x
  let D : Set V := componentFrom A.graph U xU
  have hMinU : IsMinimalClosedSeparator A U xU yU :=
    oppositeBoundaryClosure_isMinimalClosedSeparator
      A T hTclosed x y hSeparated hExactX
  have hExactU : A.functionClosure
      (gaifmanNeighborhood A.graph D) = U :=
    minimalClosedSeparator_leftBoundary_eq A U xU yU hMinU
  have hCsubD : C ⊆ D :=
    componentFrom_subset_of_cut_subset A.graph hUT x
  by_contra hNoWitness
  have hDavoidT : ∀ z : V, z ∈ D → z ∉ T := by
    intro z hzD hzT
    exact hNoWitness ⟨z, hzT, hzD.1, hzD⟩
  have hStep : ∀ {a b : {z : V // z ∉ U}},
      a.1 ∈ C →
      outsideAdjacency A.graph U a b →
      b.1 ∈ C := by
    intro a b haC hab
    have haD : a.1 ∈ D := hCsubD haC
    have hbD : b.1 ∈ D :=
      componentFrom_step A.graph U xU haD b.2 hab
    have hbNotT : b.1 ∉ T := hDavoidT b.1 hbD
    exact componentFrom_step A.graph T x haC hbNotT hab
  have hDsubC : D ⊆ C := by
    intro z hzD
    exact reachOutside_stays_in A.graph U C xU
      (componentFrom_root A.graph T x) hStep hzD.2
  have hCeqD : C = D := Set.Subset.antisymm hCsubD hDsubC
  have hT_eq_U : T = U := by
    calc
      T = A.functionClosure (gaifmanNeighborhood A.graph C) :=
        hExactX.symm
      _ = A.functionClosure (gaifmanNeighborhood A.graph D) := by
        rw [hCeqD]
      _ = U := hExactU
  have hUneT : U ≠ T :=
    (Set.ssubset_iff_subset_ne.mp hProper).2
  exact hUneT hT_eq_U.symm

end AllThoseRamseyClasses.Lifts
