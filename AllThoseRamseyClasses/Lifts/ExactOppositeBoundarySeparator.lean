import AllThoseRamseyClasses.Lifts.ClosedBoundaryIntersectionCut
import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent

/-!
# The generated opposite boundary is itself the EXACT minimal closed separator

This improves the "uncovered boundary" branch of Section 3 Claim 2.
Let T be an actual function-closed source cut separating x,y.
Assume that T is the COMPLETE generated external boundary
Cl(N(C_T(x))) of the x-component after deleting T.

Set U=Cl(N(C_T(y))) for the opposite component. Its native
function closure is contained in T, and the previously verified
component-boundary lemma shows that U still separates x and y.

There is no need to minimize among smaller closed separators:
**U itself is already a minimal closed separator.**
Indeed every smaller CLOSED separator R contained in U must
contain the intersection of the two original generated boundary
closures, which is exactly U since Cl(N(C_T(x)))=T and U⊆T.

This statement is entirely native source geometry, valid for
arbitrary functional arities and arbitrary carrier cardinality.
It needs no forbidden family, target map, canonical lift or
injectivity. It does NOT assert that the new piece is contained
in an old mixed piece or that its root retains an old root.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- If the x-component's complete generated boundary is exactly
a closed separator T of x and y, then the generated boundary
U of the opposite y-component is ITSELF a minimal closed
separator between those same original source vertices.

In particular no additional finite separator selection is needed
when U is strictly smaller than T. -/
theorem oppositeBoundaryClosure_isMinimalClosedSeparator
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x y : {z : V // z ∉ T})
    (hSepT : ¬ ReachOutside A.graph T x y)
    (hFullXBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T x)) = T) :
    IsMinimalClosedSeparator A
      (A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)))
      (outsideCutMap
        (functionalClosure_neighborhood_subset_cut A T hTclosed y) x)
      (outsideCutMap
        (functionalClosure_neighborhood_subset_cut A T hTclosed y) y) := by
  let U : Set V :=
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  let hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut A T hTclosed y
  change IsMinimalClosedSeparator A U
    (outsideCutMap hUT x) (outsideCutMap hUT y)
  have hUclosed : A.IsClosed U :=
    A.functionClosure_isClosed
      (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  have hSepTyx : ¬ ReachOutside A.graph T y x := by
    intro hYX
    exact hSepT (reachOutside_symm A.graph T hYX)
  have hSepUyx :
      ¬ ReachOutside A.graph U
        (outsideCutMap hUT y) (outsideCutMap hUT x) :=
    closureNeighborhood_separates A T hTclosed y x hSepTyx
  have hSepUxy :
      ¬ ReachOutside A.graph U
        (outsideCutMap hUT x) (outsideCutMap hUT y) := by
    intro hXY
    exact hSepUyx (reachOutside_symm A.graph U hXY)
  refine ⟨hUclosed, hSepUxy, ?_⟩
  intro R hRclosed hRU hSepR
  have hRT : R ⊆ T := hRU.trans hUT
  have hSepRT : ¬ ReachOutside A.graph R
      (outsideCutMap hRT x) (outsideCutMap hRT y) := by
    simpa only [outsideCutMap] using hSepR
  apply rootedBoundarySubset_of_smallerClosedSeparator
    A hRclosed hRT x y hSepRT
  constructor
  · intro z hzU
    rw [hFullXBoundary]
    exact hUT hzU
  · intro z hzU
    exact hzU

/-- A closed source cut R lying inside the opposite generated
boundary U and separating the same x,y must equal ALL of U.
Thus an arbitrary minimal-cut-selection step cannot shrink
the root further: the exact new root is U. -/
theorem oppositeBoundaryClosure_eq_of_closedSeparatingSubset
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x y : {z : V // z ∉ T})
    (hSepT : ¬ ReachOutside A.graph T x y)
    (hFullXBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T x)) = T)
    (R : Set V)
    (hRU : R ⊆
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)))
    (hRclosed : A.IsClosed R)
    (hSepR : ¬ ReachOutside A.graph R
      (outsideCutMap
        (hRU.trans
          (functionalClosure_neighborhood_subset_cut A T hTclosed y)) x)
      (outsideCutMap
        (hRU.trans
          (functionalClosure_neighborhood_subset_cut A T hTclosed y)) y)) :
    R = A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T y)) := by
  let U : Set V :=
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  let hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut A T hTclosed y
  have hMinU :
      IsMinimalClosedSeparator A U
        (outsideCutMap hUT x) (outsideCutMap hUT y) :=
    oppositeBoundaryClosure_isMinimalClosedSeparator
      A T hTclosed x y hSepT hFullXBoundary
  have hSepR' : ¬ ReachOutside A.graph R
      (outsideCutMap hRU (outsideCutMap hUT x))
      (outsideCutMap hRU (outsideCutMap hUT y)) := by
    simpa only [outsideCutMap] using hSepR
  have hUR : U ⊆ R :=
    hMinU.2.2 R hRclosed hRU hSepR'
  exact Set.Subset.antisymm hRU hUR

end AllThoseRamseyClasses.Lifts
