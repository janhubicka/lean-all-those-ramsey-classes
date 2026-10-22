import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Connected singleton closed separators are automatically minimal

The exact one-vertex case of Proposition `prop:sep` is much
simpler than general boundary-partner selection. If a closed
cut contains at most one source vertex, separates x and y,
and x,y are connected in the whole native functional Gaifman
graph, then no strictly smaller closed cut can separate them.
The existing forward separator theorem therefore proves that
BOTH complementary component-boundary closures equal the cut.

This removes the arbitrary boundary-partner assumption from
singleton-boundary applications once a second component is
actually identified. It does not imply a partner for a
larger generated boundary, or any lift/flip statement.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A closed singleton-or-empty cut separating a pair connected
before the deletion is necessarily a MINIMAL closed separator.
The empty-cut path also forces the cut to be nonempty. -/
theorem singletonClosedCut_isMinimal_of_connectedSeparation
    (A : Structure L V)
    (T : Set V)
    (hClosed : A.IsClosed T)
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (x y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside A.graph T x y)
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})) :
    IsMinimalClosedSeparator A T x y := by
  refine ⟨hClosed, hSep, ?_⟩
  intro S hSclosed hST hSepS t ht
  by_contra htNotS
  have hEmpty : S = ∅ := by
    ext z
    constructor
    · intro hz
      have hzEq : z = t :=
        hSingleton z t (hST hz) ht
      rw [hzEq] at hz
      exact (htNotS hz).elim
    · intro hz
      simp at hz
  cases hEmpty
  have hEmptyPath : ReachOutside A.graph (∅ : Set V)
      (outsideCutMap hST x) (outsideCutMap hST y) := by
    change ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})
    exact hConnected
  exact hSepS hEmptyPath

/-- In the same singleton-root case, BOTH actual generated
external neighbourhood closures equal T. In particular
the y-component is an exact boundary partner for the
x-component, with the original native function closure. -/
theorem singletonClosedCut_bothBoundaries_of_connectedSeparation
    (A : Structure L V)
    (T : Set V)
    (hClosed : A.IsClosed T)
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (x y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside A.graph T x y)
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})) :
    A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T x)) = T ∧
    A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T y)) = T := by
  exact minimalClosedSeparator_bothBoundaries_eq A T x y
    (singletonClosedCut_isMinimal_of_connectedSeparation
      A T hClosed hSingleton x y hSep hConnected)

end AllThoseRamseyClasses.Lifts
