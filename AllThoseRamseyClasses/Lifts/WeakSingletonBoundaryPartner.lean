import AllThoseRamseyClasses.Lifts.SingletonClosedSeparator
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation

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

The proof reuses the general closed-boundary separation theorem
for opposite-colour vertices. The singleton assumption is needed
only for minimality and the second exact boundary equation. The partner
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
      y.1 = a ∧
      ¬ ReachOutside Source.graph T (outsideCutMap hTS x) y ∧
      Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y)) = T := by
  obtain ⟨y, hYa, hSep⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree f hf x hxRight T hT hTS a haLeft
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  have hTclosed : Source.IsClosed T := by
    rw [hT]
    exact Source.functionClosure_isClosed
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S x))
  have hPath : ReachOutside Source.graph (∅ : Set U)
      (⟨(outsideCutMap hTS x).1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : U // z ∉ ∅}) := by
    change ReachOutside Source.graph (∅ : Set U)
      (⟨x.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : U // z ∉ ∅})
    simpa only [hYa] using hConnected
  have hPartner :=
    (singletonClosedCut_bothBoundaries_of_connectedSeparation
      Source T hTclosed hSingleton
      (outsideCutMap hTS x) y hSep hPath).2
  exact ⟨y, hYa, hSep, hPartner⟩

end AllThoseRamseyClasses.Lifts
