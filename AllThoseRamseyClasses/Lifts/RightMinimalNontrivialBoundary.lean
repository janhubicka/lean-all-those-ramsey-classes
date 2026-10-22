import AllThoseRamseyClasses.Lifts.SingletonRightComponentStrictSupport
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenThreeRegions
import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent

/-!
# Every right component of a minimal obstruction has at least two boundary vertices

In a full free amalgam of two forbidden-free native functional
witnesses with the same FULL original global canonical lift,
choose a finite forbidden EHN source minimizing its number of
right-exclusive SOURCE vertices.

Because the source is connected and both sides of the free
amalgam are forbidden-free, both exclusive source regions are
nonempty. The previously verified direct singleton-component
flip therefore excludes **every** right component whose entire
generated external boundary has at most one vertex.

We prove the positive structural conclusion, not merely the
negation of a singleton predicate: every such component has
two DISTINCT vertices in Cl(N(C)). These lie in the full
shared-root preimage, but their target images may coincide.
No globally injective weak map and no outer mixed piece is assumed.

This is a necessary obstruction classification under the
original full canonical lift. It does NOT assert that arbitrary
forbidden families have small boundaries, nor prove the
unrestricted Section 3 strong-amalgamation theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In a genuine forbidden source minimizing right-exclusive
source support, every right-exclusive Gaifman component outside
the shared root has at least TWO DISTINCT vertices in its
generated external boundary.

The two vertices are source vertices; this theorem does NOT
assert injectivity of their images under the original EHN map. -/
theorem minimalRightWitness_rightComponent_hasTwoBoundaryVertices
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMinRight : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight))
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget) :
    let S := weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget
    let T := w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph S x))
    ∃ u v : w.Carrier, u ∈ T ∧ v ∈ T ∧ u ≠ v := by
  classical
  dsimp
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let T : Set w.Carrier :=
    w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph S x))
  have hSclosed : w.source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft)
      w.toTarget w.homEmbedding.1
  have hTS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut
      w.source S hSclosed x
  obtain ⟨_, _, ⟨a, haLeft⟩, _, _⟩ :=
    globalForbiddenConnectedWitness_threeRegions
      F hConnected hFree hAvoidLeft hAvoidRight
      w.source w.finiteCarrier w.forbidden
      w.toTarget w.homEmbedding
  by_contra hNoTwo
  have hSingleton :
      ∀ u v : w.Carrier, u ∈ T → v ∈ T → u = v := by
    intro u v hu hv
    by_contra hne
    exact hNoTwo ⟨u, v, hu, hv, hne⟩
  exact minimalRightWitness_noSingletonRightComponent
    F hFiniteF hConnected
    Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    w hMinRight x hxRight T rfl hTS hSingleton a haLeft

end AllThoseRamseyClasses.Lifts
