import AllThoseRamseyClasses.Lifts.Claim2NoSeamIncursionBoundaryPartner
import AllThoseRamseyClasses.Lifts.Claim2PartnerActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.ConnectedComponentBoundaryNonempty
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation

/-!
# Track C: actual general-width right source flip under NO SEAM INCURSION

This composes the exact restricted source-geometric boundary-partner
criterion with the already verified SAME-Q full forbidden-source flip.
It is not a change of representation and does not use a weak-image
quotient or collapse the original functional graph language.

At an original A-exclusive source-support minimizer with a smallest
mixed old geometric piece, a B-exclusive S-component and an opposite
A-exclusive source vertex have a matching complete native generated
boundary if no strictly smaller rooted component may internally
capture a vertex of the original full common seam. The existing
full target-root preimage injectivity makes this entire boundary
injective in the weak target. Source connectedness forces the full
generated boundary to be nonempty; actual free-amalgam monochromaticity
provides the required separating opposite y.

The resulting SAME Q replacement is a GENUINE full native forbidden
source with an ACTUAL new outer geometric piece, unchanged ordered old
outer root target coordinates and global canonical piece symbol, and
strictly fewer B-only SOURCE vertices inside that actual outer piece.

**Conditional:** the no-seam-incursion and original full-seam
target-injectivity assumptions are still unresolved in the general
2019 Claim 2 proof. This theorem neither derives a valid successor
at all positive-rank states nor establishes final A-only clearing.
The numbered manuscript stays frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- General-root-width actual selected geometric B-to-A source flip,
conditional on the precise seam-cleanliness barrier and injectivity
on the original full common seam. Both conditions are explicit.
The result contains ONE genuine new forbidden source/old-symbol Q
witness with strictly lower INSIDE B-only SOURCE cardinality. -/
theorem minimalLeftWitness_noSeamIncursion_actualGeometricRightFlip
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
    (w : ForbiddenEHNWitness F Target)
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hInjOnRoot : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hMinP : ∀ Q : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      P.nonrootCount ≤ Q.nonrootCount)
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hxOld : x.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (y : {z : w.Carrier // z ∉ T})
    (hyLeft : y.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (hyOld : y.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left)
    (hNoSeamIncursion :
      ∀ (m : ℕ) (d : GeometricFunctionalPieceData w.source m),
        Set.range d.roots ⊂ T →
        ∀ r : w.Carrier,
          r ∈ weakFreeRootPart
            (sL := iLeft) (iL := jLeft) w.toTarget →
          r ∉ functionalComponentFrom w.source
            (Set.range d.roots) d.left) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData w.source m),
      0 < m ∧
      geometricPieceVertices w.source d ⊂
        geometricPieceVertices w.source P.data ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New P.width),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin P.width,
          flip (newOuter.roots i) = w.toTarget (P.data.roots i)) ∧
        geometricGlobalPieceSymbol F w.source
            w.finiteCarrier w.forbidden P.data P.positive =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter P.positive ∧
        Nat.card {v' : V' //
          v' ∈ geometricPieceVertices New newOuter ∧
          flip v' ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : w.Carrier //
          v ∈ geometricPieceVertices w.source P.data ∧
          w.toTarget v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  have hyNotB : y.1 ∉ componentFrom w.source.graph S x := by
    intro hyComponent
    have hyRight : y.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget :=
      weakFreePartition_component_right
        hFree w.toTarget w.homEmbedding.1 x hxRight hyComponent
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree w.toTarget))
        hyLeft hyRight
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 y.1)
  have hTnonempty : T.Nonempty := by
    rw [hT]
    exact functionalComponent_generatedBoundary_nonempty_of_emptyCutReach
      w.source S x y.1 hyNotB hPath
  obtain ⟨y', hy'Val, hSeparated'⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree w.toTarget w.homEmbedding
      x hxRight T hT hTS y.1 hyLeft
  have hy'Eq : y' = y := Subtype.ext hy'Val
  have hSeparated : ¬ ReachOutside w.source.graph T
      (outsideCutMap hTS x) y := by
    simpa only [hy'Eq] using hSeparated'
  have hMatchedBoundary :
      w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph T y)) = T :=
    minimalLeftWitness_noSeamIncursion_forces_matchingBoundary
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon w hMinLeft hInjOnRoot P hMinP
      x hxRight hxOld T hT hTS y hyLeft hyOld hNoSeamIncursion
  have hInjT : Set.InjOn w.toTarget T := by
    intro a ha b hb hab
    exact hInjOnRoot (hTS ha) (hTS hb) hab
  exact claim2_actualGeometricRightFlip_of_boundaryPartner
    F hFiniteF w.source w.finiteCarrier w.forbidden
    P.data P.positive
    Target w.toTarget w.homEmbedding
    Left Right jLeft jRight X iLeft iRight hFree hCommon
    P.roots_in_common
    x hxRight hxOld
    y.1 hyLeft hyOld
    T hT hTS hTnonempty
    y hSeparated hMatchedBoundary hInjT

end AllThoseRamseyClasses.Lifts
