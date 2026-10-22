import AllThoseRamseyClasses.Lifts.GlobalRightComponentDirectPartnerFlip
import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent

/-!
# Source-side boundary coverage for the arbitrary-width B-component flip

Let S be the complete common-root preimage of a weak EHN map into
a true full native functional free amalgam, and let B be the actual
right-exclusive Source minus S component containing x. Define
T=Cl(N(B)) ⊆ S. Even when T has arbitrarily many vertices:

* B remains EXACTLY the component of x after deleting T;
* every LEFT-exclusive source vertex a lies outside that component,
  and is therefore separated from x by T.

Thus the existence of a LEFT-side boundary partner is equivalent
to one remaining geometric INCLUSION: the generated external
neighborhood closure of the a-component after deleting T
must COVER every vertex of T. The opposite inclusion is automatic
because T is function-closed.

This is a much sharper geometric obstruction than an opaque
"partner exists" premise. It does not claim that coverage follows
from maximal-lift agreement, mixed-piece minimality, regularity, or
forbidden image closure. Under coverage and injectivity of f ON T,
the already verified direct arbitrary-width flip applies WITHOUT
any outer mixed piece and strictly decreases source right support.
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

/-- If the generated boundary of the opposite LEFT component
covers T, it is automatically EQUAL to T: the reverse inclusion
comes from the closedness of T, not an additional premise.

This produces exactly the actual boundary partner needed for the
source-attached arbitrary-width flip; no singleton condition. -/
theorem weakRightComponent_oppositeCoverage_hasPartner
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
    (haLeft : a ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hCoverage : ∀ y : {z : U // z ∉ T}, y.1 = a →
      T ⊆ Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y))) :
    ∃ y : {z : U // z ∉ T},
      y.1 = a ∧
      ¬ ReachOutside Source.graph T (outsideCutMap hTS x) y ∧
      Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y)) = T := by
  obtain ⟨y, hYa, hSep⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree f hf x hxRight T hT hTS a haLeft
  have hTclosed : Source.IsClosed T := by
    rw [hT]
    exact Source.functionClosure_isClosed
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x))
  have hBoundLe : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) ⊆ T :=
    functionalClosure_neighborhood_subset_cut
      Source T hTclosed y
  have hBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T :=
    Set.Subset.antisymm hBoundLe (hCoverage y hYa)
  exact ⟨y, hYa, hSep, hBoundary⟩

end AllThoseRamseyClasses.Lifts
