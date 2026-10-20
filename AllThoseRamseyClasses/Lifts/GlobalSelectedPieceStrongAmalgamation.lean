import AllThoseRamseyClasses.Lifts.GlobalSelectedMixedBoundaryCriterion
import AllThoseRamseyClasses.Lifts.GlobalShadowAvoidanceFromGeometricConditions

/-!
# Original global canonical-lift strong AP from SELECTED-piece geometry

The remaining shadow-avoidance argument can be discharged with
two explicit source-attached assumptions at support-minimal
forbidden EHN witnesses in genuine functional free amalgams:

* Each genuine geometric piece root inside the common-root
  preimage is pairwise covered by full irreducible source tests,
  so its TARGET root images are injective.
* Every smallest genuinely mixed source piece has SOME
  opposite-colour pair whose components after deleting the
  full common-root preimage have the original piece root
  inside both generated neighborhood closures.

The latter existential condition is weaker than the previous
condition requiring boundary inclusions for ALL opposite pairs.
Both are OPEN under the printed arbitrary regular image-closed
family hypotheses. Hence these are verified CONDITIONAL class
theorems, not an unrestricted Section 3 proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Named source-geometric conditions for each actual
support-minimal forbidden weak witness, not an assumed
free-amalgamation conclusion. This statement is not derived
from regularity or homomorphism-embedding image closure. -/
def GlobalMinimalWitnessSelectedGeometricConditions
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {UX UA UB UT : Type}
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
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)),
    GeometricPieceRootsPairwiseCoveredOn w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) ∧
    MinimalMixedPieceSelectedBoundaries w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)


/-- The already formalized stronger two-condition hypothesis
(common-root-preimage pairwise coverage and universal opposite-pair
boundaries) implies the WEAKER selected-piece condition.

This is an implication of hypothesis STRENGTH, not a claim that
either condition follows from the 2019 paper's assumptions. -/
theorem globalMinimalWitnessSelectedGeometricConditions_of_stronger
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hStrong : GlobalMinimalWitnessGeometricConditions F) :
    GlobalMinimalWitnessSelectedGeometricConditions F := by
  intro UX UA UB UT Target Left Right
    jLeft jRight X iLeft iRight
    hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  obtain ⟨hAllPairs, hEveryBoundary⟩ :=
    hStrong Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  have hPiece : GeometricPieceRootsPairwiseCoveredOn w.source S := by
    intro n d hRoots x y hx hy hne
    exact hAllPairs x y (hRoots hx) (hRoots hy) hne
  have hSelected :
      MinimalMixedPieceSelectedBoundaries w.source S AOnly BOnly :=
    minimalMixedPieceSelectedBoundaries_of_allPairs
      w.source S AOnly BOnly
      (by intro x hx; exact hx.2)
      (by intro y hy; exact hy.2)
      hEveryBoundary
  exact ⟨hPiece, hSelected⟩

/-- Native free-amalgam forbidden avoidance for the ORIGINAL global
canonical lift, conditional on the two source-geometric obligations.
The strong-amalgam shadow theorem itself is an actual proof, not
a conclusion postulated as a premise. -/
theorem globalCanonicalShadowFree_of_selectedGeometricConditions
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hGeometry : GlobalMinimalWitnessSelectedGeometricConditions F) :
    GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) := by
  intro UX UA UB UT X Left Right Target
    iLeft iRight jLeft jRight
    hFree hAgree hAvoidLeft hAvoidRight
  let hCommon : CommonGlobalCanonicalLift
      F X Left Right iLeft iRight :=
    CommonGlobalCanonicalLift.ofAgreeOn
      F X Left Right iLeft iRight hAgree
  by_contra hBad
  have hExists : Nonempty (ForbiddenEHNWitness F Target) :=
    not_avoidsGlobalFunctionalEHN_hasWitness F Target hBad
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target (fullFreeLeftExclusiveTarget iLeft jLeft) hExists
  obtain ⟨hPairCover, hBoundaries⟩ :=
    hGeometry Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hAvoidLeft hAvoidRight w hMin
  exact minimalGlobalForbiddenWitness_no_of_piecewiseCover_selectedBoundaries
    F hFiniteF hConnected Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    hAvoidLeft hAvoidRight w hMin hPairCover hBoundaries

/-- Genuine finite strong amalgamation of the original regular
maximal global-trace age, CONDITIONAL on the two explicit source
checks rather than an opaque assumed shadow-avoidance result.
It constructs a real finite expanded amalgam with two FULL
expanded embeddings and exactly prescribed overlap. -/
theorem globalFiniteMaximalTraceAge_strongAmalgamation_of_selectedGeometricConditions
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hGeometry : GlobalMinimalWitnessSelectedGeometricConditions F)
    {VX VY VZ : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ)
    (hY : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) Y)
    (hZ : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) Z)
    (fY : Structure.Embedding X Y)
    (fZ : Structure.Embedding X Z) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN F A) T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T),
        ∀ y : VY, ∀ z : VZ,
          jY y = jZ z ↔
            ∃ x : VX, y = fY x ∧ z = fZ x := by
  exact globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree
    F (fun {W : Type} (A : Structure L W) =>
      AvoidsGlobalFunctionalEHN F A)
    hRegular
    (globalCanonicalShadowFree_of_selectedGeometricConditions
      F hFiniteF hConnected hGeometry)
    X Y Z hY hZ fY fZ

end AllThoseRamseyClasses.Lifts
