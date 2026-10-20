import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart

/-!
# Matching source-component boundaries construct a GENUINE geometric piece

Let S be a function-closed source cut, and let C,D be distinct
source Gaifman components outside S. If their generated external
neighborhood closures agree, write T = Cl(N(C)) = Cl(N(D)).

The exact boundary-component theorem shows that C and D remain
precisely the same components after deleting T, and T ⊆ S is
closed. Since the original components were distinct, T still
separates them. Its two component boundary closures are both
literally T; the verified converse of the minimal-separator
proposition therefore says T is a MINIMAL closed separator.

For a finite source, enumerate its whole root T to produce an
actual geometric forbidden-source piece (once the source itself
belongs to the forbidden family), with its selected nonroot
component EXACTLY C. This gives a concrete sufficient condition
for a one-sided component to admit a genuine source piece
rooted in the common-root preimage.

The hypothesis that the two component boundaries agree is
explicit; it is not derived from unflippability or forbidden
source minimality. No weak image quotient or target injectivity.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- If two different components outside a CLOSED cut S have
exactly the same generated neighborhood closure T, then T
is itself a genuine inclusion-minimal function-closed
separator of the same distinguished vertices. -/
theorem minimalClosedSeparator_of_matchingComponentBoundaries
    (A : Structure L V)
    (S : Set V) (hS : A.IsClosed S)
    (x y : {v : V // v ∉ S})
    (hNotReach : ¬ ReachOutside A.graph S x y)
    (hSameBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S y)) =
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x))) :
    let T := A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
    let hTS : T ⊆ S :=
      functionalClosure_neighborhood_subset_cut A S hS x
    IsMinimalClosedSeparator A T
      (outsideCutMap hTS x) (outsideCutMap hTS y) := by
  dsimp only
  let T : Set V := A.functionClosure
    (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
  have hTS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut A S hS x
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  let yT : {v : V // v ∉ T} := outsideCutMap hTS y
  have hClosedT : A.IsClosed T :=
    A.functionClosure_isClosed
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
  have hCx :
      componentFrom A.graph T xT =
        componentFrom A.graph S x :=
    componentBoundaryClosure_preserves_exact_component A S hS x
  have hBoundaryY :
      gaifmanNeighborhood A.graph
        (componentFrom A.graph S y) ⊆ T := by
    intro z hz
    have hzInY : z ∈ A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph S y)) :=
      A.subset_functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph S y)) hz
    simpa only [hSameBoundary] using hzInY
  have hCy :
      componentFrom A.graph T yT =
        componentFrom A.graph S y := by
    apply Set.Subset.antisymm
    · intro z hz
      exact reachOutside_stays_in_avoid_boundary
        A.graph T (componentFrom A.graph S y) yT
        (componentFrom_root A.graph S y) hBoundaryY hz.2
    · exact componentFrom_subset_of_cut_subset A.graph hTS y
  have hSepT : ¬ ReachOutside A.graph T xT yT := by
    intro hPath
    have hyCxT : y.1 ∈ componentFrom A.graph T xT :=
      ⟨yT.2, hPath⟩
    rw [hCx] at hyCxT
    exact hNotReach hyCxT.2
  apply minimalClosedSeparator_of_bothBoundaries_eq
    A T hClosedT xT yT hSepT
  · rw [hCx]
  · rw [hCy]
    exact hSameBoundary

/-- In a FINITE source, two distinct S-components with equal
generated neighborhood closures determine an ACTUAL geometric
source piece. The selected nonroot component is exactly the
given original S-component, not a superset enlarged by
shrinking the deleted cut.

The chart has literal native functional structure. Its root
lies in S, and its two selected vertices are unchanged. -/
theorem finite_matchingComponentBoundaries_hasGeometricPiece
    [Finite V]
    (A : Structure L V)
    (S : Set V) (hS : A.IsClosed S)
    (x y : {v : V // v ∉ S})
    (hNotReach : ¬ ReachOutside A.graph S x y)
    (hSameBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S y)) =
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x))) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData A n),
      Set.range d.roots ⊆ S ∧
      d.left.1 = x.1 ∧ d.right.1 = y.1 ∧
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph S x := by
  let T : Set V := A.functionClosure
    (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
  have hTS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut A S hS x
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  let yT : {v : V // v ∉ T} := outsideCutMap hTS y
  have hMin : IsMinimalClosedSeparator A T xT yT :=
    minimalClosedSeparator_of_matchingComponentBoundaries
      A S hS x y hNotReach hSameBoundary
  obtain ⟨n, d, hRoots, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart A T xT yT hMin
  have hComp :
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph S x := by
    -- Transport the dependent root subtype before identifying its
    -- two surviving distinguished vertices.
    cases hRoots
    have hLeftEq : d.left = outsideCutMap hTS x :=
      Subtype.ext hLeft
    rw [hLeftEq]
    exact componentBoundaryClosure_preserves_exact_component
      A S hS x
  exact ⟨n, d, by simpa only [hRoots] using hTS,
    hLeft, hRight, hComp⟩

end AllThoseRamseyClasses.Lifts
