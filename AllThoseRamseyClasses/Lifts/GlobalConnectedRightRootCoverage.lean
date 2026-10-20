import AllThoseRamseyClasses.Lifts.GlobalRootPairwiseTestCoverage
import AllThoseRamseyClasses.Lifts.MinimalGeometricCutComponentPath

/-!
# Connected opposite region: a collision must evade irreducible source tests

Consider a support-minimal forbidden EHN witness into the actual
functional free amalgam of two forbidden-free sides with compatible
FULL original Section 3 canonical lifts.

If all right-exclusive SOURCE vertices are in one Gaifman component
after deleting the common-root preimage S, the selected minimal
closed-separator left component C cannot contain any right-exclusive
source vertex: C is disjoint from the S-complement component of the
chosen right root (MinimalGeometricCutComponentPath).

Combining this with the original-global Claim 1 dichotomy gives an
unconditional geometric necessary condition: the genuine positive-
width selected source root is NOT pairwise covered by full
irreducible source tests. In particular, if S itself is pairwise
covered, there is no such support-minimal forbidden obstruction.

This does NOT prove that the right-exclusive region is connected
for an arbitrary forbidden map, nor does it prove the multicomponent
Claim 2 or general strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under a single right-exclusive Gaifman component, an original
minimal forbidden obstruction has a genuine positive-width selected
root which fails pairwise irreducible-test coverage. This is an
actual piece selected from the forbidden source, not a quotient. -/
theorem minimalGlobalForbiddenWitness_uncoveredRoot_of_connectedRight
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
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hAllRight : ∀ (y z : w.Carrier)
      (hy : y ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
      (hz : z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      ReachOutside w.source.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
        ⟨y, hy.2⟩ ⟨z, hz.2⟩) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
      ¬ RootPairsCoveredByIrreducibleTests
        w.source (Set.range d.roots) := by
  obtain ⟨n, d, hn, hRoots, _hLeft, hRight, _hPiece, hCases⟩ :=
    minimalGlobalForbiddenWitness_uncoveredRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  refine ⟨n, d, hn, hRoots, ?_⟩
  rcases hCases with hUncovered | ⟨z, hzComponent, hzRight⟩
  · exact hUncovered
  · let S : Set w.Carrier :=
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
    have hNoPath : ¬ ReachOutside w.source.graph S
        (⟨d.right.1, hRight.2⟩ : {v : w.Carrier // v ∉ S})
        (⟨z, hzRight.2⟩ : {v : w.Carrier // v ∉ S}) :=
      minimalGeometricPiece_component_not_reachable_from_right
        w.source d S hRoots
        ⟨d.right.1, hRight.2⟩ rfl hzComponent hzRight.2
    exact False.elim (hNoPath (hAllRight d.right.1 z hRight hzRight))

/-- If the preimage of the common full root is pairwise covered by
irreducible FULL tests in the original forbidden source, then a
support-minimal obstruction cannot simultaneously have a single
right-exclusive component. Only this restricted configuration
is excluded; the general collision and multicomponent cases remain. -/
theorem minimalGlobalForbiddenWitness_no_connectedRight_of_pairCover
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
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hCovered : RootPairsCoveredByIrreducibleTests w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (hAllRight : ∀ (y z : w.Carrier)
      (hy : y ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
      (hz : z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      ReachOutside w.source.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
        ⟨y, hy.2⟩ ⟨z, hz.2⟩) :
    False := by
  obtain ⟨n, d, _hn, hRoots, hUncovered⟩ :=
    minimalGlobalForbiddenWitness_uncoveredRoot_of_connectedRight
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin hAllRight
  have hCoveredPiece :
      RootPairsCoveredByIrreducibleTests
        w.source (Set.range d.roots) := by
    intro x y hx hy hne
    exact hCovered x y (hRoots hx) (hRoots hy) hne
  exact hUncovered hCoveredPiece

end AllThoseRamseyClasses.Lifts
