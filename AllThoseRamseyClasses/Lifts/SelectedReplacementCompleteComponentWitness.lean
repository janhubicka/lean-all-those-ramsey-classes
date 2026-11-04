import AllThoseRamseyClasses.Lifts.SelectedReplacementAllPrivateConnected
import AllThoseRamseyClasses.Lifts.SelectedReplacementInternalGeneratedRoot
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# One selected-Q witness has BOTH a complete boundary and all-private connectivity

The genuine selected functional replacement piece Q previously has
two separately verified source-geometry interfaces:

* an existing complete-root-boundary theorem finds some Q-private
  vertex d with Cl_Q(N(component(Q\U,d))) = U;
* all-private connectivity proves that some (potentially DIFFERENT)
  private vertex x has every Q-private vertex in component(Q\U,x).

Since d is Q-private, it belongs to the component of x.
Root-avoiding paths are symmetric, so every private vertex
reachable from x is reachable from d. We can therefore use the
boundary witness d as the connectivity witness too.

This removes a subtle unjustified witness-identification step
from the genuine nested outer-context carrier application.
A generic profile-equivalent rooted extension, without actual
geometric selected membership, does NOT satisfy the theorem's
hypothesis. No weak EHN target-image map or arbitrary finite
component assumption occurs.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A genuinely selected canonical replacement Q has ONE actual
Q-private vertex whose root-complement component (i) generates
the WHOLE original native functional root and (ii) contains
EVERY Q-private vertex.

The two statements refer to exactly the same chosen vertex,
not merely to potentially different private components. -/
theorem selectedReplacementPiece_completeComponentWitness
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (R : Structure L (Fin n))
    (Q : FunctionalRootExtension R)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        R (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n) :
    ∃ d : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding},
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) d)) =
          Set.range Q.rootEmbedding ∧
      (∀ q : Q.Carrier,
        q ∉ Set.range Q.rootEmbedding →
          q ∈ componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) d) := by
  obtain ⟨d, hdBoundary⟩ :=
    selectedReplacementPiece_has_internalGeneratedRoot
      F R Q hSelected
  obtain ⟨x, hxAll⟩ :=
    selectedReplacementPiece_allPrivate_connected
      F R Q hSelected
  have hdInX :
      d.1 ∈ componentFrom Q.str.graph
        (Set.range Q.rootEmbedding) x :=
    hxAll d.1 d.2
  have hdToX :
      ReachOutside Q.str.graph (Set.range Q.rootEmbedding) d x :=
    reachOutside_symm Q.str.graph (Set.range Q.rootEmbedding)
      hdInX.2
  refine ⟨d, hdBoundary, ?_⟩
  intro q hq
  have hqInX :
      q ∈ componentFrom Q.str.graph
        (Set.range Q.rootEmbedding) x :=
    hxAll q hq
  exact ⟨hq, hdToX.trans hqInX.2⟩

end AllThoseRamseyClasses.Lifts
