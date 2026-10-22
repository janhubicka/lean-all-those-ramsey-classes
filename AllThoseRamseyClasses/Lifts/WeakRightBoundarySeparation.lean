import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import PartiteConstruction.Functional.WeakInvariant

/-!
# A generated right-component boundary separates all opposite-colour vertices

Let S be the complete shared-root preimage of a genuine weak EHN
source map into a native functional free amalgam, B a right-only
component of Source minus S, and T=Cl(N(B)) its generated boundary.

The exact component-survival theorem proves B is STILL the exact
x-component after shrinking the deleted set S to T. Every
left-exclusive source vertex a lies outside B by the native
monochromatic component property, hence x and a are separated
after deleting T, for ARBITRARY boundary width.

This pure source-geometric lemma does not use canonical lifts,
piece flips, target image injectivity, minimal forbidden sources,
or any assumption that T has a boundary partner.
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

/-- WITHOUT a singleton assumption, the generated boundary of a
right-exclusive S-component already separates it from EVERY
left-exclusive source vertex. The actual left vertex is returned
unchanged, not an arbitrary new witness.

This theorem uses the complete native functional closure and
allows globally noninjective weak EHN source maps. -/
theorem weakRightComponent_leftVertex_separatedByBoundary
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := sL) (iL := iL) f)
    (a : U)
    (haLeft : a ∈ weakFreeLeftPart (sL := sL) (iL := iL) f) :
    ∃ y : {z : U // z ∉ T},
      y.1 = a ∧
      ¬ ReachOutside Source.graph T (outsideCutMap hTS x) y := by
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
    cases hT
    exact componentBoundaryClosure_preserves_exact_component
      Source S hSclosed x
  have hSep : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y := by
    intro hReach
    have haComp : a ∈ componentFrom Source.graph T
        (outsideCutMap hTS x) := ⟨haNotT, hReach⟩
    rw [hCompT] at haComp
    exact haNotB haComp
  exact ⟨y, rfl, hSep⟩

end AllThoseRamseyClasses.Lifts
