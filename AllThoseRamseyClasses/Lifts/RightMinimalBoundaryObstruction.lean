import AllThoseRamseyClasses.Lifts.BoundaryPartnerRightSupportDescent
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import AllThoseRamseyClasses.Lifts.IrreducibleTestRootCollisions
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Minimal RIGHT-support obstruction: a partner forces boundary image collisions

This is the actual source-witness minimization consequence of the
strict B-to-A flip. An old mixed piece P contains a right-only
component B outside the entire shared-root preimage S, and a
left-only vertex a in P's selected component.

If B has a genuine closed-boundary partner, connectedness
of the forbidden source forces its generated boundary T to
be nonempty. A RIGHT-support-minimal forbidden witness
therefore cannot be injective on T. Hence T is NOT pairwise
covered by full irreducible source tests.

The support minimum here is on the RIGHT side, not the LEFT
minimum used in the original Claim 1 proof. These two minima
are not interchangeable: a B-to-A flip may increase LEFT
support. Consequently the unrestricted printed Claim 2 is
NOT proved by this module.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual right-support-minimal forbidden EHN map, with a
mixed source piece P containing a right-exclusive component
and a left-exclusive vertex, cannot have a genuine
boundary-partner component with injective target boundary.
The forbidden-family connectedness hypothesis supplies
positive root width automatically.

The explicit colliding source pair and failure of
irreducible-test coverage form a SOURCE-side necessary condition, not a blanket image
injectivization or a strong-amalgamation conclusion. -/
theorem minimalRightWitness_boundaryPartner_forcesCollision
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
    (hMinRight : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ≤
        v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight))
    {n : ℕ} (P : GeometricFunctionalPieceData w.source n)
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxOld : x.1 ∈ functionalComponentFrom w.source
      (Set.range P.roots) P.left)
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (y : {z : w.Carrier // z ∉ T})
    (hSep : ¬ ReachOutside w.source.graph T
      (outsideCutMap hTS x) y)
    (hYBoundary : w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y)) = T)
    (a : w.Carrier)
    (haOld : a ∈ functionalComponentFrom w.source
      (Set.range P.roots) P.left)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget) :
    (∃ u v : w.Carrier,
        u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ w.toTarget u = w.toTarget v) ∧
      ¬ RootPairsCoveredByIrreducibleTests w.source T := by
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 y.1)
  have hTnonempty : T.Nonempty := by
    by_contra hNot
    have hEmpty : T = ∅ := by
      ext z
      constructor
      · intro hz
        exact (hNot ⟨z, hz⟩).elim
      · intro hz
        simp at hz
    cases hEmpty
    change ¬ ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : w.Carrier // z ∉ ∅}) at hSep
    exact hSep hPath
  have hBadInjectivity : ¬ Set.InjOn w.toTarget T := by
    intro hInjT
    obtain ⟨m, Q, hQroot, hProper,
        V', New, hNew, flip, hFlip, hDecrease⟩ :=
      boundaryPartner_properRightPiece_strictRightSupport
        F hFiniteF w.source w.finiteCarrier w.forbidden
        Target w.toTarget w.homEmbedding
        Left Right jLeft jRight X iLeft iRight
        hFree hCommon P hRoots x hxOld hxRight
        T hT hTS y hSep hYBoundary
        a haOld haLeft hTnonempty hInjT
    let replacement : ForbiddenEHNWitness F Target := {
      Carrier := V'
      finiteCarrier := hFiniteF New hNew
      source := New
      forbidden := hNew
      toTarget := flip
      homEmbedding := hFlip
    }
    have hStrict :
        replacement.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) <
        w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) := hDecrease
    exact (minimalForbiddenEHNWitness_no_strict_drop
      (fullFreeRightExclusiveTarget iRight jRight)
      w hMinRight replacement) hStrict
  constructor
  · classical
    by_contra hNoCollision
    apply hBadInjectivity
    intro u hu v hv huv
    by_contra hne
    exact hNoCollision ⟨u, v, hu, hv, hne, huv⟩
  · intro hCovered
    apply hBadInjectivity
    exact ehn_injOn_of_rootPairsCoveredByIrreducibleTests
      w.source Target w.toTarget w.homEmbedding T hCovered

end AllThoseRamseyClasses.Lifts
