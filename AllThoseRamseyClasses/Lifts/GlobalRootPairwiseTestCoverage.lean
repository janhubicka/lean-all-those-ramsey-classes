import AllThoseRamseyClasses.Lifts.IrreducibleTestRootCollisions
import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn
import AllThoseRamseyClasses.Lifts.GlobalOneSidedCollisionObstruction

/-!
# Pairwise irreducible-test condition in the original Section 3 argument

An EHN weak map cannot collapse two source vertices if a full
irreducible source test contains both. Thus a collision in the ordered
root of a minimal forbidden geometric piece forces a specific failure
of pairwise irreducible-test coverage of that source root.

Using the verified 20 October minimal-obstruction dichotomy, we
replace its bare root-collision alternative by this purely SOURCE
geometric obstruction. Conversely, if the entire shared-root preimage
is pairwise covered, the existing formalization constructs a genuine
smallest mixed piece, without requiring global injectivity of the weak
source map.

These are exact reductions, not a proof that root coverage always
holds or that a mixed piece admits the Claim 2 strict descent.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In a minimal forbidden EHN witness with a genuine one-sided
geometric piece, the piece's separator roots are NOT pairwise
covered by full irreducible source tests, even if the tests
are allowed to extend beyond the closed root. -/
theorem minimalGlobalOneSidedPiece_rootFailsIrreducibleTestCoverage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
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
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hNoRight : ∀ z : w.Carrier,
      z ∈ functionalComponentFrom w.source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget) :
    ¬ RootPairsCoveredByIrreducibleTests
      w.source (Set.range d.roots) := by
  have hCollision :
      ¬ Function.Injective
        (fun i : Fin n => w.toTarget (d.roots i)) :=
    minimalGlobalOneSidedPiece_rootImagesCollide
      F hFiniteF Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon w hMin
      d hn hRoots hNoRight hLeft
  exact geometricRoot_not_pairwiseIrreducibleTestCovered_of_collision
    w.source d Target w.toTarget w.homEmbedding hCollision

/-- Every support-minimal connected forbidden weak obstruction to
a genuine full native free amalgam with common FULL original
canonical lifts has a positive-width geometric separator piece
which either fails pairwise irreducible-test coverage (in the
FULL source), or is genuinely mixed.

Unlike a bare 'noninjective target root tuple', failure of
coverage refers only to the source structure and its full
irreducible tests. No image-quotient injection is asserted. -/
theorem minimalGlobalForbiddenWitness_uncoveredRoot_or_mixedPiece
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
      d.left.1 ∈
        weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
      d.right.1 ∈
        weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget ∧
      geometricFunctionalRootedPattern w.source d ∈
        forbiddenGeometricFunctionalPieces F n ∧
      (¬ RootPairsCoveredByIrreducibleTests
          w.source (Set.range d.roots) ∨
        ∃ z : w.Carrier,
          z ∈ functionalComponentFrom w.source
            (Set.range d.roots) d.left ∧
          z ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget) := by
  obtain ⟨n, d, hn, hRoots, hLeft, hRight, hPiece, hCases⟩ :=
    minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  refine ⟨n, d, hn, hRoots, hLeft, hRight, hPiece, ?_⟩
  rcases hCases with hCollision | hMixed
  · exact Or.inl
      (geometricRoot_not_pairwiseIrreducibleTestCovered_of_collision
        w.source d Target w.toTarget w.homEmbedding hCollision)
  · exact Or.inr hMixed

/-- Pairwise irreducible-test coverage of the SHARED-ROOT PREIMAGE
is sufficient to obtain the actual smallest mixed geometric piece,
without global injectivity of the forbidden map. This assumes
coverage of the source preimage; it does NOT establish it. -/
theorem minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_pairCover
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
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)) :
    ∃ P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      ∀ Q : MixedGeometricPiece w.source
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
        (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
        (weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
        P.nonrootCount ≤ Q.nonrootCount := by
  have hInjOn :
      Set.InjOn w.toTarget
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) :=
    ehn_injOn_of_rootPairsCoveredByIrreducibleTests
      w.source Target w.toTarget w.homEmbedding
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      hCovered
  exact minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
    F hFiniteF hConnected
    Target Left Right jLeft jRight X iLeft iRight
    hTargetFree hCommon hAvoidLeft hAvoidRight w hMin hInjOn

end AllThoseRamseyClasses.Lifts
