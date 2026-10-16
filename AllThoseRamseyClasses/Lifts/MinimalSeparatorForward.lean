import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# Minimal closed separators: neighbourhood-closure necessity

First direction of Proposition `prop:sep` in Hubička--Nešetřil (2019).
For any two vertices on opposite sides of a closed cut R,
inclusion-minimality among closed separating cuts forces R to be
the generated function closure of EACH component's external
Gaifman neighbourhood.

The converse (if the two closures equal R, then R is minimal)
requires a second argument with closed component unions and
transport of components through a smaller cut. It remains separate
until formalized, and is not silently asserted here.

Unlike a graph-only argument this uses the ACTUAL functionClosure
in the ambient structure, so no generated closure vertex is treated
as if directly adjacent to a component.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A fixed pair of vertices lies in distinct components of a closed
cut R, and every smaller closed cut that still separates the pair
must equal R. The pair is given as actual vertices outside R. -/
def IsMinimalClosedSeparator
    (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R}) : Prop :=
  A.IsClosed R ∧
    ¬ ReachOutside A.graph R x y ∧
    ∀ (S : Set V) (hSclosed : A.IsClosed S) (hSR : S ⊆ R),
      ¬ ReachOutside A.graph S
          (outsideCutMap hSR x) (outsideCutMap hSR y) →
        R ⊆ S

/-- The closed hull of a component neighbourhood still separates the
chosen vertices. Paths avoiding this hull cannot leave the original
component, because they cannot cross its external neighbourhood. -/
theorem closureNeighborhood_separates
    (A : Structure L V) (R : Set V) (hR : A.IsClosed R)
    (x y : {v : V // v ∉ R})
    (hsep : ¬ ReachOutside A.graph R x y) :
    let S := A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x))
    let hSR : S ⊆ R :=
      functionalClosure_neighborhood_subset_cut A R hR x
    ¬ ReachOutside A.graph S
      (outsideCutMap hSR x) (outsideCutMap hSR y) := by
  dsimp
  intro hpath
  let C : Set V := componentFrom A.graph R x
  let S : Set V := A.functionClosure (gaifmanNeighborhood A.graph C)
  have hBoundary : gaifmanNeighborhood A.graph C ⊆ S :=
    A.subset_functionClosure (gaifmanNeighborhood A.graph C)
  have hStart : (outsideCutMap
      (functionalClosure_neighborhood_subset_cut A R hR x) x).1 ∈ C :=
    componentFrom_root A.graph R x
  have hyC : y.1 ∈ C :=
    reachOutside_stays_in_avoid_boundary A.graph S C
      (outsideCutMap
        (functionalClosure_neighborhood_subset_cut A R hR x) x)
      hStart hBoundary hpath
  exact hsep hyC.2

/-- The first necessity equation in Proposition `prop:sep`.
The minimality assumption really quantifies over ALL smaller
closed separating sets, not merely arbitrary vertex cuts. -/
theorem minimalClosedSeparator_leftBoundary_eq
    (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R})
    (hmin : IsMinimalClosedSeparator A R x y) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) = R := by
  apply Set.Subset.antisymm
  · exact functionalClosure_neighborhood_subset_cut A R hmin.1 x
  · let S := A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x))
    have hSclosed : A.IsClosed S :=
      A.functionClosure_isClosed
        (gaifmanNeighborhood A.graph (componentFrom A.graph R x))
    have hSR : S ⊆ R :=
      functionalClosure_neighborhood_subset_cut A R hmin.1 x
    apply hmin.2.2 S hSclosed hSR
    exact closureNeighborhood_separates A R hmin.1 x y hmin.2.1

/-- Minimal closed separation is symmetric in its two distinguished
vertices, because Gaifman paths are reversible. -/
theorem minimalClosedSeparator_swap
    (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R})
    (hmin : IsMinimalClosedSeparator A R x y) :
    IsMinimalClosedSeparator A R y x := by
  refine ⟨hmin.1, ?_, ?_⟩
  · intro hyx
    exact hmin.2.1 (reachOutside_symm A.graph R hyx)
  · intro S hSclosed hSR hNoYX
    apply hmin.2.2 S hSclosed hSR
    intro hXY
    exact hNoYX (reachOutside_symm A.graph S hXY)

/-- Both boundary closures equal the minimal cut. This is the entire
forward implication of Proposition `prop:sep` for the actual
function-closed structure setting. -/
theorem minimalClosedSeparator_bothBoundaries_eq
    (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R})
    (hmin : IsMinimalClosedSeparator A R x y) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) = R ∧
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R y)) = R := by
  exact ⟨minimalClosedSeparator_leftBoundary_eq A R x y hmin,
    minimalClosedSeparator_leftBoundary_eq A R y x
      (minimalClosedSeparator_swap A R x y hmin)⟩

end AllThoseRamseyClasses.Lifts
