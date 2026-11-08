import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# Nonempty native generated boundary from full Gaifman connectedness

The source component \`C = componentFrom A.graph S x\` of a
vertex x outside any deleted cut S may have empty external
neighbourhood if the ambient source is disconnected. But if
a vertex a outside C is connected to x by a genuine source
Gaifman path (the empty-cut path), an edge along that path
must leave C. The external neighbourhood is therefore NONEMPTY
and so is its complete function-generated closure.

This fact uses no singleton assumption, no target weak-map
injectivity, no finite source restriction, no minimality and no
bound on relation/function arity. It is a source-native path
argument, valid with full set-valued functions and nullaries.

In Section 3 Claim 2, x is a B-exclusive source vertex in
one monochromatic component of the full target-seam preimage,
while an A-exclusive anchor a cannot lie in that component.
The connected-forbidden-source hypothesis supplies the full
source path. Thus nonemptiness of the component's generated
boundary should not be an independent oracle in the general
partner/smaller-root dichotomy or singleton-boundary subcase.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type}

/-- If x is connected in the FULL source to a vertex a outside
its S-avoiding connected component, then that component has an
actual Gaifman neighbour outside itself.

In particular, the full path cannot be contained in the selected
S-component; one of its edges must cross into the deleted cut S.
No connectedness property of the whole source other than this
particular full path is needed. -/
theorem componentFrom_neighborhood_nonempty_of_emptyCutReach
    (A : Structure L V) (S : Set V)
    (x : {v : V // v ∉ S}) (a : V)
    (haOutside : a ∉ componentFrom A.graph S x)
    (hPath : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅})) :
    (gaifmanNeighborhood A.graph
      (componentFrom A.graph S x)).Nonempty := by
  by_contra hNoBoundary
  let C : Set V := componentFrom A.graph S x
  have hEdgeClosed : ∀ {v w : V},
      v ∈ C → GaifmanAdjacent A.graph v w → w ∈ C := by
    intro v w hvC hedge
    by_cases hwS : w ∈ S
    · have hwNotC : w ∉ C := by
        intro hwC
        exact hwC.1 hwS
      have hwBoundary :
          w ∈ gaifmanNeighborhood A.graph C :=
        ⟨hwNotC, v, hvC, hedge⟩
      exact False.elim (hNoBoundary ⟨w, hwBoundary⟩)
    · exact componentFrom_step A.graph S x hvC hwS hedge
  have hReachInside :
      ∀ y : {v : V // v ∉ (∅ : Set V)},
        ReachOutside A.graph (∅ : Set V)
          (⟨x.1, by simp⟩ : {v : V // v ∉ ∅}) y →
        y.1 ∈ C := by
    intro y hReach
    induction hReach with
    | refl =>
        exact componentFrom_root A.graph S x
    | @tail v w hPre hEdge ih =>
        exact hEdgeClosed ih hEdge
  exact haOutside (hReachInside ⟨a, by simp⟩ hPath)

/-- Under the same exact full-source path hypothesis, the
ENTIRE native function-generated external boundary of the
S-component is nonempty. No artificial generator or finite
cut assumption is used: every genuine neighbourhood vertex
belongs to the generated closure by its defining property. -/
theorem functionalComponent_generatedBoundary_nonempty_of_emptyCutReach
    (A : Structure L V) (S : Set V)
    (x : {v : V // v ∉ S}) (a : V)
    (haOutside : a ∉ componentFrom A.graph S x)
    (hPath : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅})) :
    (A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph S x))).Nonempty := by
  obtain ⟨z, hz⟩ :=
    componentFrom_neighborhood_nonempty_of_emptyCutReach
      A S x a haOutside hPath
  refine ⟨z, ?_⟩
  intro Closed hClosed hSeed
  exact hSeed hz

end AllThoseRamseyClasses.Lifts
