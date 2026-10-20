import AllThoseRamseyClasses.Lifts.GlobalConnectedRightRootCoverage
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# The two remaining configurations in the original global lift

The original Section 3 proof starts with a forbidden weak EHN witness
into a genuine full native free amalgam of forbidden-free sides,
assuming their original quotient-indexed canonical lifts agree on
the common full root.

The verified minimal source-support argument produces a genuine
positive-width minimal closed-separator piece. The original Claim 1
flip proves that its source root is either NOT pairwise covered by
full irreducible tests, or its chosen left component is mixed.

In the mixed case, the right-exclusive vertex inside that component
cannot be joined to the distinguished right-exclusive vertex outside
the common-root preimage: such a path would contradict the original
closed separator. We thus obtain an unconditional alternative with
two explicit right-exclusive vertices in DIFFERENT Gaifman components
of the source outside the full root preimage.

This is the exact remaining collision/multicomponent dichotomy for
the original lift, without injectivizing the forbidden weak map,
changing the old partial functions, or postulating the Claim 2 flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the actual hypotheses of the original-global Claim 1,
a minimal forbidden witness produces a genuine positive-width source
piece whose root fails pairwise irreducible-test coverage, OR two
right-exclusive source vertices lie in different Gaifman components
after removing the common-root preimage.

The second alternative is stronger than merely saying the selected
piece is mixed. The disconnection follows from a checked path
contradiction for the actual minimal function-closed separator. -/
theorem minimalGlobalForbiddenWitness_uncoveredRoot_or_disconnectedRight
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
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
      (¬ RootPairsCoveredByIrreducibleTests
          w.source (Set.range d.roots) ∨
        ∃ (y z : w.Carrier)
          (hy : y ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft)
            (iR := jRight) w.toTarget)
          (hz : z ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft)
            (iR := jRight) w.toTarget),
          ¬ ReachOutside w.source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
            ⟨y, hy.2⟩ ⟨z, hz.2⟩) := by
  obtain ⟨n, d, hn, hRoots, _hLeft, hRight, _hPiece, hCases⟩ :=
    minimalGlobalForbiddenWitness_uncoveredRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  refine ⟨n, d, hn, hRoots, ?_⟩
  rcases hCases with hUncovered | ⟨z, hzComponent, hzRight⟩
  · exact Or.inl hUncovered
  · right
    refine ⟨d.right.1, z, hRight, hzRight, ?_⟩
    exact minimalGeometricPiece_component_not_reachable_from_right
      w.source d
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      hRoots ⟨d.right.1, hRight.2⟩ rfl
      hzComponent hzRight.2

/-- The collision/multicomponent alternative holds without an
arbitrarily chosen minimal forbidden map: if there is ANY forbidden
weak EHN witness in the target, first select a genuine support
minimizer, then obtain one of the two explicit source obstructions.

In particular, all conclusions concern the same actual finite
forbidden source used by the selected minimum. -/
theorem globalForbiddenWitness_exists_uncoveredRoot_or_disconnectedRight
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
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ (w : ForbiddenEHNWitness F Target),
      (∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
        0 < n ∧
        Set.range d.roots ⊆
          weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
        (¬ RootPairsCoveredByIrreducibleTests
            w.source (Set.range d.roots) ∨
          ∃ (y z : w.Carrier)
            (hy : y ∈ weakFreeRightPart
              (sL := iLeft) (iL := jLeft)
              (iR := jRight) w.toTarget)
            (hz : z ∈ weakFreeRightPart
              (sL := iLeft) (iL := jLeft)
              (iR := jRight) w.toTarget),
            ¬ ReachOutside w.source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
              ⟨y, hy.2⟩ ⟨z, hz.2⟩) := by
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support F Target
      (fullFreeLeftExclusiveTarget iLeft jLeft) hExists
  refine ⟨w, hMin, ?_⟩
  exact minimalGlobalForbiddenWitness_uncoveredRoot_or_disconnectedRight
    F hFiniteF hConnected
    Target Left Right jLeft jRight X iLeft iRight
    hTargetFree hCommon hAvoidLeft hAvoidRight w hMin

end AllThoseRamseyClasses.Lifts
