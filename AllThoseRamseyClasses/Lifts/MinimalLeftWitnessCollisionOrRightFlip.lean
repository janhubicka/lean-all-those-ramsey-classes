import AllThoseRamseyClasses.Lifts.MinimalMixedAuxiliaryCollisionOrFlip
import AllThoseRamseyClasses.Lifts.GlobalMinimalForbiddenObstructionDichotomy
import AllThoseRamseyClasses.Lifts.GlobalPiecewiseRootCoverageCriterion

/-!
# A LEFT-minimal forbidden witness: actual root collision OR strict B-support drop

This is a source-matched high-level conclusion from the verified
original-global Claim 1 and the arbitrary-width closed separator
geometry, without assuming a priori a mixed source piece, an
auxiliary minimal cut, injectivity of the forbidden map or
existence of a flippable B-only piece.

The previously verified original minimal-obstruction dichotomy
starts from a finite connected forbidden weak EHN map into an
ACTUAL full functional free amalgam of two forbidden-free witnesses
with a common FULL original quotient-indexed canonical lift.
It selects a positive-width source piece. Either its TARGET root
images collide, or its left component is genuinely mixed.

In the second case choose a smallest mixed source piece. The
auxiliary-cut result of MinimalMixedAuxiliaryCollisionOrFlip
automatically produces another positive-width piece, with its
root wholly in the same common-root preimage, such that either:

* its TARGET root images collide; or
* a real proper B-only source piece flips from Right to Left
  through the original full canonical lift, giving a SECOND
  actual forbidden EHN witness with strictly fewer RIGHT-
  exclusive SOURCE vertices.

Thus every LEFT-support minimizer produces a concrete genuine
root-image collision OR an actual strictly smaller B-support
witness. No reference to an arbitrary image-quotient injection.

We also export the conditional corollary under a weaker,
source-geometric hypothesis: every positive-width genuine
minimal-separator root inside S is pairwise covered by FULL
irreducible source tests. EHN then makes only THOSE ordered
root images injective; injectivity of the entire S is not needed.

Neither theorem contradicts LEFT-support minimality by itself.
A B→A flip can increase LEFT support, and its contextual outer
piece/profile must be controlled through any further flips.
The root-coverage hypothesis is NOT established from the
published general regular HE-image-closed family assumptions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- **Unconditional source-geometric obstruction dichotomy** for
an actual LEFT-support-minimal forbidden weak EHN witness in the
original full canonical lift.

Either there is a genuine positive-width minimal closed separator
with its entire root in the common seam preimage and NONINJECTIVE
ordered TARGET images, or there exists another ACTUAL forbidden
weak EHN witness to the SAME target with STRICTLY smaller
original RIGHT-exclusive SOURCE support.

No mixed source piece, new separator, root-injectivity premise,
boundary partner or available flip is supplied externally.
This is not an assertion of forbidden-freeness of the target. -/
theorem minimalLeftWitness_rootCollision_or_strictRightReplacement
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
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    (∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
      ¬ Function.Injective
        (fun i : Fin n => w.toTarget (d.roots i))) ∨
    (∃ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) <
      w.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight)) := by
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  obtain ⟨n, d, hn, hRoots, hLeft, _hRight, _hPattern, hCases⟩ :=
    minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hAvoidLeft hAvoidRight w hMinLeft
  rcases hCases with hCollide | hMixedB
  · exact Or.inl ⟨n, d, hn, hRoots, hCollide⟩
  · let P0 : MixedGeometricPiece w.source S AOnly BOnly := {
      width := n
      data := d
      positive := hn
      roots_in_common := hRoots
      left_mixed := ⟨d.left.1,
        functionalComponentFrom_root w.source
          (Set.range d.roots) d.left, hLeft⟩
      right_mixed := hMixedB
    }
    obtain ⟨P, hMinP⟩ :=
      exists_minimalMixedGeometricPiece
        w.source S AOnly BOnly ⟨P0⟩
    obtain ⟨m, Q, hm, hInside, hAlt⟩ :=
      minimalLeftMixedPiece_auxiliaryCollision_or_properRightFlip
        F hFiniteF hConnected
        Target Left Right jLeft jRight X iLeft iRight
        hFree hCommon w hMinLeft P hMinP
    rcases hAlt with hCollision | hFlip
    · exact Or.inl ⟨m, Q, hm,
        (fun z hz => (hInside hz).1), hCollision⟩
    · obtain ⟨_Qright, _hProper, _hNoLeft,
        V', New, hNew, flip, hFlipMap, hStrict⟩ := hFlip
      let newWitness : ForbiddenEHNWitness F Target := {
        Carrier := V'
        finiteCarrier := hFiniteF New hNew
        source := New
        forbidden := hNew
        toTarget := flip
        homEmbedding := hFlipMap
      }
      exact Or.inr ⟨newWitness, hStrict⟩

/-- Without any injectivity assumption on the common-root
preimage, it is sufficient for a strict B-source-support
replacement that every genuine separator root inside the
common root be pairwise covered by full irreducible SOURCE
tests. The EHN clause then injects just those root tuples.

This condition can be strictly weaker than InjOn S, and is
the already established source-geometric interface of #563.
It is NOT automatically supplied by the general 2019 regular
family and image-closure hypotheses. -/
theorem minimalLeftWitness_strictRightReplacement_of_piecewiseTestCover
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
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hPieceCover : GeometricPieceRootsPairwiseCoveredOn w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)) :
    ∃ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) <
      w.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) := by
  rcases minimalLeftWitness_rootCollision_or_strictRightReplacement
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight w hMinLeft with
    ⟨n, d, _hn, hRoots, hCollision⟩ | hDrop
  · have hInjective :
        Function.Injective (fun i : Fin n => w.toTarget (d.roots i)) :=
      geometricRootImage_injective_of_piecewiseCover
        w.source
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
        Target w.toTarget w.homEmbedding hPieceCover d hRoots
    exact False.elim (hCollision hInjective)
  · exact hDrop

end AllThoseRamseyClasses.Lifts
