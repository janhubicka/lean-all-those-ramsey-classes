import AllThoseRamseyClasses.Lifts.WeakRightBoundaryCoverage
import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceConditionalStrongAmalgamation

/-!
# The original global lift has strong AP under an exact component-boundary test

The original Section 3 strong-amalgamation proof can be reorganized
WITHOUT a minimal mixed outer piece. Take a finite forbidden weak
EHN witness minimizing RIGHT-exclusive SOURCE support in the true
native free amalgam of two forbidden-free witnesses with agreeing
FULL original canonical lifts.

It suffices that, in such a right-minimal witness, SOME right-side
source component B and SOME left-side source vertex a satisfy:
  (i) the entire generated boundary T=Cl(N(B)) is covered by
      the generated boundary of the a-component after deleting T;
 (ii) every pair of vertices of T lies in a full irreducible
      source test (hence the weak target map is injective ON T).

The full partner needed for the source flip is CONSTRUCTED from (i)
by the separate native boundary-coverage lemma; (ii) rules out the
collision forced by the strict right-support flip. Neither condition
follows from the manuscript's general connectedness, regularity, or
closure-under-HE-images hypothesis. They are kept as an explicit
SOURCE-geometric assumption, not hidden in a proof claim.

Under the explicit hypothesis this module proves genuine forbidden
shadow avoidance and then constructs an actual finite strong
amalgam of the ORIGINAL global maximal-trace lift, with complete
native function fibres and full expanded embeddings.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For each actual minimum of ORIGINAL right-exclusive source
support, a right S-component has an opposite LEFT source vertex
whose component covers its whole generated boundary, and that
boundary is pairwise covered by full irreducible source tests.

This condition is about one concrete component of one concrete
weak EHN forbidden source; it does not assume the strong
amalgamation conclusion and it does not assert global injectivity. -/
def GlobalMinimalRightBoundaryCoverage
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {UX UA UB UT : Type}
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
    (hMinRight : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight)),
    ∃ x : {z : w.Carrier // z ∉
        weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget},
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget ∧
      ∃ a : w.Carrier,
        a ∈ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) w.toTarget ∧
        (let T : Set w.Carrier := w.source.functionClosure
            (gaifmanNeighborhood w.source.graph
              (componentFrom w.source.graph
                (weakFreeRootPart
                  (sL := iLeft) (iL := jLeft) w.toTarget) x))
         (∀ y : {z : w.Carrier // z ∉ T}, y.1 = a →
           T ⊆ w.source.functionClosure
             (gaifmanNeighborhood w.source.graph
               (componentFrom w.source.graph T y))) ∧
         RootPairsCoveredByIrreducibleTests w.source T)

/-- Native free-amalgam forbidden avoidance under the explicit
source-boundary hypothesis. This is a genuine theorem about the
ORIGINAL full quotient-indexed canonical lifts, not an assumed
forbidden-free shadow predicate. -/
theorem globalCanonicalShadowFree_of_minimalRightBoundaryCoverage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hGeometry : GlobalMinimalRightBoundaryCoverage F) :
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
  obtain ⟨w, hMinRight⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target (fullFreeRightExclusiveTarget iRight jRight) hExists
  obtain ⟨x, hxRight, a, haLeft, hCoverage, hTestCover⟩ :=
    hGeometry Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight w hMinRight
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let T : Set w.Carrier :=
    w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph S x))
  have hSclosed : w.source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft)
      w.toTarget w.homEmbedding.1
  have hTS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut
      w.source S hSclosed x
  have hContradiction :=
    minimalRightWitness_oppositeCoverage_forcesCollision
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      w hMinRight x hxRight T rfl hTS
      a haLeft hCoverage
  exact hContradiction.2 hTestCover

/-- A REAL finite strong amalgam in the original regular
global maximal-trace age. All additional source-boundary
hypotheses remain explicit; no arbitrary Claim 2 conclusion
is asserted. -/
theorem globalFiniteMaximalTraceAge_strongAmalgamation_rightCoverage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hGeometry : GlobalMinimalRightBoundaryCoverage F)
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
    (globalCanonicalShadowFree_of_minimalRightBoundaryCoverage
      F hFiniteF hConnected hGeometry)
    X Y Z hY hZ fY fZ

end AllThoseRamseyClasses.Lifts
