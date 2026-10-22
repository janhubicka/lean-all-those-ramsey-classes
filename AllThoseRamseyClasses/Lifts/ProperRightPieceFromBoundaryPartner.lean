import AllThoseRamseyClasses.Lifts.BoundaryPartnerProperSubpiece
import AllThoseRamseyClasses.Lifts.GeometricPieceRightFactor

/-!
# Genuine proper right-exclusive sub-piece with a FULL EHN right witness

The original Section 3 Claim 2 flips proper B-only sub-pieces
of a globally smallest mixed forbidden-source piece.

The independent source geometry proves that a right-exclusive
Source-minus-S component B inside a genuine old piece P,
when equipped with the exact boundary partner needed to make
T=Cl(N(B)) an inclusion-minimal functional separator, gives
a genuine new rooted piece Q with Q properly contained in P.

This module additionally checks the actual weak source map.
Every Gaifman component of a finite weak EHN source outside
the full common-root preimage S is monochromatic: if B
contains a right-exclusive vertex x it has no left-exclusive
vertex. The checked right-side cancellation lemma therefore
builds a real EHN homomorphism-embedding of the WHOLE Q
into the full Right target witness, preserving the exact
native relations and all partial function fibres.

There is no blanket injectivization of f, no unverified
piece existence assumption, and no source map image quotient.
What remains to flip Q with the original distinct-root
canonical lift is injectivity of its target ordered roots,
positive width, common full lifted-root data, and then
the Claim 2 support/minimality argument.
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

/-- A genuine mixed old source piece P containing a selected
right-exclusive Source-minus-S component B and an additional
left-exclusive vertex a has a PROPER geometric sub-piece Q
mapping weakly into the full Right target, whenever B has an
actual generated-boundary partner.

The result includes equality of the full NEW piece root with
T, proper containment of full piece VERTEX SETS (not merely
components), and the ENTIRE native EHN right map. -/
theorem weakRightComponent_partner_has_properRightFactor
    [Finite U]
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxOld : x.1 ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : {z : U // z ∉ T})
    (hSep : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y)
    (hYBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T)
    (a : U)
    (haOld : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (haLeft : a ∈ weakFreeLeftPart (sL := sL) (iL := iL) f) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData Source m),
      Set.range Q.roots = T ∧
      geometricPieceVertices Source Q ⊂
        geometricPieceVertices Source P ∧
      ∃ pRight : geometricPieceVertices Source Q → F,
        (geometricFunctionalPiece Source Q).IsEHNHomomorphismEmbedding
          Right pRight ∧
        ∀ z, iR (pRight z) = f z.1 := by
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  have hSclosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed (sL := sL) (iL := iL) f hf.1
  have haNotB : a ∉ componentFrom Source.graph S x := by
    intro haB
    have haRight : a ∈ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f :=
      weakFreePartition_component_right hFree f hf.1
        x hxRight haB
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f)) haLeft haRight
  obtain ⟨m, Q, hQroot, hQcomponent, hProper⟩ :=
    finite_boundaryPartner_gives_proper_geometricSubpiece
      Source P S T hSclosed hRoots
      x hxOld hT hTS y hSep hYBoundary
      a haOld haLeft.2 haNotB
  have hQrootsS : Set.range Q.roots ⊆ S := by
    rw [hQroot]
    exact hTS
  obtain ⟨pRight, hpRight, hMap⟩ :=
    weakGeometricPiece_factor_right_of_exactSharedRootComponent
      hFree f hf Q hQrootsS x hxRight hQcomponent
  exact ⟨m, Q, hQroot, hProper, pRight, hpRight, hMap⟩

end AllThoseRamseyClasses.Lifts
