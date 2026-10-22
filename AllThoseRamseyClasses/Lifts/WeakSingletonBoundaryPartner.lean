import AllThoseRamseyClasses.Lifts.SingletonClosedSeparator
import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents

/-!
# A singleton boundary has an ACTUAL partner in a connected mixed source

For a weak forbidden-source map into the full native free
amalgam, let S be the entire preimage of the common root, and
let B be a right-exclusive connected component of Source \\ S.
Its generated full functional external boundary is T=Cl(N(B)).

If T has at most one vertex and there is a left-exclusive
source vertex a connected in the original source to a chosen
right-exclusive vertex x of B, then the component of a after
deleting T is an ACTUAL boundary partner of B:
* it is distinct from the x-component after deleting T;
* its generated external neighbourhood closure is EXACTLY T.

The proof uses the true monochromatic S-component property,
exact component preservation on shrinking S to T, and the
minimality of any connected singleton separator. The partner
is **constructed**, not separately assumed. No EHN map or
image quotient is made injective, and all original function
fibres remain unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The LEFT-exclusive source vertex itself supplies the
boundary-partner component when the RIGHT component has a
singleton generated boundary and the original two source
vertices are joined by a Gaifman path.

The output is exactly the previously explicit y / separation /
full generated-boundary-equality hypothesis required to build
a genuine geometric piece from the right component. -/
theorem weakRightComponent_singletonBoundary_hasPartner
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := sL) (iL := iL) f)
    (hSingleton : ∀ u v : U, u ∈ T → v ∈ T → u = v)
    (a : U)
    (haLeft : a ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hConnected : ReachOutside Source.graph (∅ : Set U)
      (⟨x.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨a, by simp⟩ : {z : U // z ∉ ∅})) :
    ∃ y : {z : U // z ∉ T},
      ¬ ReachOutside Source.graph T (outsideCutMap hTS x) y ∧
      Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y)) = T := by
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  have hSclosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed (sL := sL) (iL := iL) f hf.1
  have haNotS : a ∉ S := haLeft.2
  have haNotT : a ∉ T := fun ht => haNotS (hTS ht)
  let y : {z : U // z ∉ T} := ⟨a, haNotT⟩
  have haNotB : a ∉ componentFrom Source.graph S x := by
    intro haB
    have haRight :
        a ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f :=
      weakFreePartition_component_right
        hFree f hf.1 x hxRight haB
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f))
        haLeft haRight
  have hCompT :
      componentFrom Source.graph T (outsideCutMap hTS x) =
        componentFrom Source.graph S x := by
    rw [hT]
    exact componentBoundaryClosure_preserves_exact_component
      Source S hSclosed x
  have hSep : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y := by
    intro hReach
    have haComp : a ∈ componentFrom Source.graph T
        (outsideCutMap hTS x) := ⟨haNotT, hReach⟩
    rw [hCompT] at haComp
    exact haNotB haComp
  have hTclosed : Source.IsClosed T := by
    rw [hT]
    exact Source.functionClosure_isClosed
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S x))
  have hPath : ReachOutside Source.graph (∅ : Set U)
      (⟨(outsideCutMap hTS x).1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : U // z ∉ ∅}) := by
    simpa only using hConnected
  have hPartner := (singletonClosedCut_bothBoundaries_of_connectedSeparation
    Source T hTclosed hSingleton (outsideCutMap hTS x) y hSep hPath).2
  exact ⟨y, hSep, hPartner⟩

end AllThoseRamseyClasses.Lifts
