import AllThoseRamseyClasses.Lifts.CommonGlobalCanonicalLift
import AllThoseRamseyClasses.Lifts.GlobalCanonicalInducedTrace
import AllThoseRamseyClasses.Lifts.EHNFullSideMinimalObstruction

/-!
# Track D: complete induced common global lift iff equality of piece profiles

The original 2019 maximal-trace strong amalgamation API asks for the
two genuine native F-free side witnesses to induce the SAME canonical
added piece-class predicates on the common FULL old-language root:
  GlobalCanonicalLiftsAgreeOn F iA iB.

Several previously verified Track D collision/defect reductions used
the apparently stronger CommonGlobalCanonicalLift structure, carrying
a common expanded root with two FULL embeddings into the two ambient
canonical lifts.

For FULL native old root embeddings these interfaces are EQUIVALENT.
The forward direction was already proved by the common-lift agreement
API. The reverse direction uses the EXACT full induced canonical
trace on X as seen in A, and the relational agreement to construct
a second FULL embedding of that same actual native expanded root
into the canonical lift of B. Full old-language relation/function
tables agree because the starting iA and iB are FULL embeddings,
not because a weak quotient is being mistaken for a full target.

This discharges an API presentation mismatch, NOT the mathematical
strong-amalgamation/forbidden-source flip obligation. In particular
the common-lift structure records PROFILE AGREEMENT; it does not
assert the original witness maximality predicate. Maximality is
used upstream to produce such an agreement from age witnesses.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Construct a concrete FULL common original global functional
lift from equality of ALL added piece-class relations on the
same FULL native old root.

The chosen expanded root is literally the induced canonical
trace seen from A; its shadow is exactly X, its inclusion in
A is the previously verified FULL trace embedding, and the
relation agreement supplies a second FULL embedding into B
on the EXACT prescribed original vertex coordinates.

No forbidden-family, regularity, maximality, K-membership,
full free-amalgam or EHN witness assumption is required. -/
noncomputable def commonGlobalCanonicalLift_of_agreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iA iB) :
    CommonGlobalCanonicalLift F X A B iA iB := by
  let LiftX : Structure (globalFunctionalPieceLanguage F) UX :=
    globalCanonicalInducedTrace F iA
  let intoB : Structure.Embedding LiftX
      (globalFunctionalCanonicalLift F B) := by
    apply functionalWithExtraBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (fun s xs =>
        (globalFunctionalCanonicalLift F A).rel
          (.inr s) (iA ∘ xs))
      (functionalCanonicalExtraBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F)
        (globalFunctionalPieceRepresentatives F) B)
      iB
    intro s xs
    exact (hAgree s xs).symm
  exact {
    lifted := LiftX
    shadow_eq := globalCanonicalInducedTrace_shadow F iA
    intoA := globalCanonicalInducedTrace_into_witness F iA
    intoB := intoB
    intoA_verts := fun _ => rfl
    intoB_verts := fun _ => rfl
  }

/-- EXACT equivalence of the two verified original 2019 full
common-lift compatibility APIs. The old partial/set-valued
functions and relations are preserved via the FULL root
embeddings, not deduced from the added predicate equivalence.
A common expanded root may be obtained from either ambient
canonical induced trace once this agreement holds. -/
theorem commonGlobalCanonicalLift_nonempty_iff_agreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) :
    Nonempty (CommonGlobalCanonicalLift F X A B iA iB) ↔
      GlobalCanonicalLiftsAgreeOn F iA iB := by
  constructor
  · rintro ⟨hCommon⟩
    exact hCommon.agreeOn F
  · intro hAgree
    exact ⟨commonGlobalCanonicalLift_of_agreeOn
      F iA iB hAgree⟩

/-- The earlier fully verified original Section 3 exact
target-incidence trichotomy can be invoked with JUST the
GlobalCanonicalLiftsAgreeOn F iLeft iRight hypothesis used
by the finite maximal-trace strong-amalgamation API.

No extra unproved CommonGlobalCanonicalLift compatibility
witness is needed: the full common trace is constructed above.
This bridges the interface to the TRUE global maximal-trace
age without changing the still-open full-native shadow
avoidance or source-flip obligations. -/
theorem minimalForbiddenWitness_fullyUnliftableSideIncidence_or_mixedPiece_of_agreement
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ (w : ForbiddenEHNWitness F Target),
      (∀ t : ForbiddenEHNWitness F Target,
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      (HasFullSideUnliftableFunctionIncident
          w.source Left Right Target jLeft jRight w.toTarget ∨
       HasFullSideUnliftableRelationIncident
          w.source Left Right Target jLeft jRight w.toTarget ∨
       ∃ (v : ForbiddenEHNWitness F Target),
         Function.Injective v.toTarget ∧
         (∀ t : ForbiddenEHNWitness F Target,
           v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
             t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
         ∃ P : MixedGeometricPiece v.source
           (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
           (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
           (weakFreeRightPart
             (sL := iLeft) (iL := jLeft) (iR := jRight) v.toTarget),
           ∀ Q : MixedGeometricPiece v.source
             (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
             (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
             (weakFreeRightPart
               (sL := iLeft) (iL := jLeft) (iR := jRight) v.toTarget),
             P.nonrootCount ≤ Q.nonrootCount) := by
  let hCommon : CommonGlobalCanonicalLift
      F X Left Right iLeft iRight :=
    commonGlobalCanonicalLift_of_agreeOn F iLeft iRight hAgree
  exact exists_minimalForbiddenWitness_fullyUnliftableSideIncidence_or_mixedPiece
    F hFiniteF hConnected hImage
    Target Left Right jLeft jRight X iLeft iRight
    hTargetFree hCommon hAvoidLeft hAvoidRight hExists

end AllThoseRamseyClasses.Lifts
