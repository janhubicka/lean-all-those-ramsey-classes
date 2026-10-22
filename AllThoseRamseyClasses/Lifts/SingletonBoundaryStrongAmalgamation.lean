import AllThoseRamseyClasses.Lifts.RightMinimalNontrivialBoundary
import AllThoseRamseyClasses.Lifts.GlobalShadowAvoidanceFromGeometricConditions
import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceConditionalStrongAmalgamation

/-!
# A concrete, sufficient source-boundary condition for the original global lift

The unrestricted printed Section 3 strong-amalgamation proof has two
remaining hard issues: colliding images of multivertex piece roots and
the multicomponent Claim 2 flip. There is an independently reusable
sufficient case where neither issue can arise.

Assume that for every forbidden source, EVERY function-closed cut S,
and EVERY actual Gaifman component of Source \\ S, its generated
external neighbourhood boundary Cl(N(C)) has at most ONE vertex.
This is an EXPLICIT, strong source-family condition; it is **not**
derived from connectedness, regularity or image closure.

If a forbidden weak EHN map entered the true full free amalgam
of two forbidden-free witnesses with matching FULL original
canonical lifts, choose one with minimal right-exclusive SOURCE
support. The already proved singleton flip/obstruction theorem
forces every right component to have TWO DISTINCT boundary
vertices, contradicting the source-family condition.

Thus the original global maximal-trace age has a genuine finite
strong amalgam whenever the family is additionally regular.
This is a FULL class theorem for an explicitly restricted family,
not an unconditional proof of the printed `lem:amalgamationstr`.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every component of every closed-cut complement in every
forbidden native source attaches through at most ONE vertex
of the complete generated external Gaifman neighbourhood.

This is stronger than saying all *minimal* separators have
width at most one. In particular the printed generic regularity
hypothesis does not imply it. -/
def GlobalForbiddenSingletonBoundaries
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {V : Type} (Source : Structure L V),
    F Source →
    ∀ (S : Set V), Source.IsClosed S →
    ∀ (x : {z : V // z ∉ S}),
      ∀ u v : V,
        u ∈ Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph S x)) →
        v ∈ Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph S x)) →
        u = v

/-- An ACTUAL full free amalgam with matching original global
canonical piece-class relations remains free of the forbidden
family under the explicit singleton-generated-boundary condition.

No arbitrary source map is assumed injective; the proof uses
the genuine right-support minimizer and the verified positive
two-boundary obstruction in the original source. -/
theorem globalCanonicalShadowFree_of_singletonBoundaries
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hSingleton : GlobalForbiddenSingletonBoundaries F) :
    GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) := by
  classical
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
  obtain ⟨hSclosed, _, _, ⟨b, hbRight⟩, _⟩ :=
    globalForbiddenConnectedWitness_threeRegions
      F hConnected hFree hAvoidLeft hAvoidRight
      w.source w.finiteCarrier w.forbidden
      w.toTarget w.homEmbedding
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let x : {z : w.Carrier // z ∉ S} :=
    ⟨b, hbRight.2⟩
  obtain ⟨u, v, hu, hv, hne⟩ :=
    minimalRightWitness_rightComponent_hasTwoBoundaryVertices
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hAvoidLeft hAvoidRight
      w hMinRight x hbRight
  exact hne (hSingleton w.source w.forbidden S hSclosed x
    u v hu hv)

/-- A finite STRONG amalgam in the original global maximal-trace
expanded age, with full native functional shadows, for every
regular connected forbidden family satisfying the explicit
singleton-generated-boundary condition.

This is a genuine finite lifted structure and full embeddings
with the exact prescribed intersection, not just a conditional
application with an assumed shadow-amalgamation principle. -/
theorem globalFiniteMaximalTraceAge_strongAmalgamation_singletonBoundaries
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hSingleton : GlobalForbiddenSingletonBoundaries F)
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
    (globalCanonicalShadowFree_of_singletonBoundaries
      F hFiniteF hConnected hSingleton)
    X Y Z hY hZ fY fZ

end AllThoseRamseyClasses.Lifts
