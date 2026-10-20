import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward

/-!
# A component survives replacing a closed cut by its own boundary closure

Let S be a function-closed vertex set of an arbitrary native
functional structure A, and C one actual Gaifman component
of A minus S. Write T = Cl_A(N_A(C)) for the generated closure
of the whole external Gaifman neighborhood of C.

The already verified component-neighborhood theorem yields
T ⊆ S. More precisely, deleting T leaves EXACTLY the same
component C, not merely a subset of C:

* every S-avoiding path is automatically T-avoiding (T ⊆ S);
* every T-avoiding path starting in C remains in C, because
  its first exit would cross the external neighborhood of C,
  which is contained in T.

The proof handles the full functional Gaifman graph, including
output/input edges and all arities, uses actual generated closure
rather than ordinary adjacency, and requires neither finiteness
nor a homomorphism-embedding map.

This is a reusable genuine piece-localization tool for the 2019
Claim 2 analysis. It does not imply that T is a minimal separator,
or that the corresponding piece is flippable or forbidden.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The exact external-neighborhood closure of a source component
is function-closed and stays within any containing CLOSED cut. -/
theorem componentBoundaryClosure_closed_subset_cut
    (A : Structure L V) (S : Set V)
    (hS : A.IsClosed S) (x : {v : V // v ∉ S}) :
    A.IsClosed
        (A.functionClosure
          (gaifmanNeighborhood A.graph (componentFrom A.graph S x))) ∧
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)) ⊆ S := by
  exact ⟨A.functionClosure_isClosed
    (gaifmanNeighborhood A.graph (componentFrom A.graph S x)),
    functionalClosure_neighborhood_subset_cut A S hS x⟩

/-- Replacing the entire function-closed cut S by the SMALLER
function-closed neighborhood boundary T = Cl(N(C)) preserves
EXACTLY the selected source Gaifman component C.

This is an equality of source vertex sets, not a claim about
target weak images or full induced embeddings. -/
theorem componentBoundaryClosure_preserves_exact_component
    (A : Structure L V) (S : Set V)
    (hS : A.IsClosed S) (x : {v : V // v ∉ S}) :
    componentFrom A.graph
      (A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)))
      (outsideCutMap
        (functionalClosure_neighborhood_subset_cut A S hS x) x) =
      componentFrom A.graph S x := by
  let C : Set V := componentFrom A.graph S x
  let T : Set V := A.functionClosure (gaifmanNeighborhood A.graph C)
  have hTS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut A S hS x
  have hBoundary : gaifmanNeighborhood A.graph C ⊆ T :=
    A.subset_functionClosure (gaifmanNeighborhood A.graph C)
  have hxC : x.1 ∈ C := componentFrom_root A.graph S x
  apply Set.Subset.antisymm
  · intro z hz
    have hzC : z ∈ C :=
      reachOutside_stays_in_avoid_boundary
        A.graph T C (outsideCutMap hTS x)
        hxC hBoundary hz.2
    exact hzC
  · exact componentFrom_subset_of_cut_subset
      A.graph hTS x

end AllThoseRamseyClasses.Lifts
