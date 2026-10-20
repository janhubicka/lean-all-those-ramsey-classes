import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedBoundaryCriterion
import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceConditionalStrongAmalgamation
import AllThoseRamseyClasses.Lifts.CommonGlobalLiftIff

/-!
# The original global lift: exact source-geometric conditions for strong AP

The remaining native shadow-free-amalgam lemma follows from two
source-attached conditions on every support-minimal forbidden EHN
witness in an actual full functional free amalgam with compatible
original canonical lifts:

1. Every pair in the common-root PREIMAGE is covered by a full
   irreducible test of its forbidden source.
2. For a smallest genuinely mixed source piece, its root lies in
   the generated neighborhood closures of BOTH source components
   containing any selected opposite-exclusive vertices after
   deleting the common-root preimage.

The existing pair-cover lemma implies root-preimage injectivity;
the checked conditional Claim 2 then supplies strict mixed-piece
descent, ruling out the forbidden witness. Native shadow avoidance
and genuine strong amalgamation of finite maximal global traces
follow by previously verified constructions.

THESE TWO CONDITIONS ARE NOT YET DERIVED FROM THE PRINTED
HYPOTHESES OF REGULARITY AND HOMOMORPHISM-EMBEDDING IMAGE CLOSURE.
The conditional theorem below is not the unrestricted 2019 result.
No frozen manuscript text is changed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The exact two original-source conditions that would close the
published global canonical-lift shadow avoidance proof.
This is a named mathematical HYPOTHESIS, not an established property
of an arbitrary regular, image-closed forbidden family. -/
def GlobalMinimalWitnessGeometricConditions
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
    RootPairsCoveredByIrreducibleTests w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) ∧
    MinimalMixedPieceTwoBoundaries w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)

/-- Every failure of Forb_EHN(F) supplies a literal forbidden finite
weak EHN witness; no injective-image reduction is used. -/
theorem not_avoidsGlobalFunctionalEHN_hasWitness
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT)
    (hBad : ¬ AvoidsGlobalFunctionalEHN F Target) :
    Nonempty (ForbiddenEHNWitness F Target) := by
  classical
  by_contra hNone
  apply hBad
  intro U Source hFinite hF f hf
  exact hNone ⟨{
    Carrier := U
    finiteCarrier := hFinite
    source := Source
    forbidden := hF
    toTarget := f
    homEmbedding := hf
  }⟩

/-- Native free-amalgam forbidden avoidance for the ORIGINAL global
canonical lift, conditional on the two source-geometric obligations.
The strong-amalgam shadow theorem itself is an actual proof, not
a conclusion postulated as a premise. -/
theorem globalCanonicalShadowFree_of_minimalGeometricConditions
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hGeometry : GlobalMinimalWitnessGeometricConditions F) :
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
  exact minimalGlobalForbiddenWitness_no_of_pairCover_twoBoundaries
    F hFiniteF hConnected Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    hAvoidLeft hAvoidRight w hMin hPairCover hBoundaries

/-- Genuine finite strong amalgamation of the original regular
maximal global-trace age, CONDITIONAL on the two explicit source
checks rather than an opaque assumed shadow-avoidance result.
It constructs a real finite expanded amalgam with two FULL
expanded embeddings and exactly prescribed overlap. -/
theorem globalFiniteMaximalTraceAge_strongAmalgamation_of_minimalGeometricConditions
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hGeometry : GlobalMinimalWitnessGeometricConditions F)
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
    (globalCanonicalShadowFree_of_minimalGeometricConditions
      F hFiniteF hConnected hGeometry)
    X Y Z hY hZ fY fZ

end AllThoseRamseyClasses.Lifts
