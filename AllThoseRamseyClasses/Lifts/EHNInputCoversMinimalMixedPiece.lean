import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredRelationInput
import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn

/-!
# Track D: exact conditional normalization-to-mixed-piece handoff

Under the PRINTED tuple-surjective forbidden-image closure axiom and
the separately EXPLICIT source irreducible-test cover predicates for
both relation and function inputs, the previous proof constructs an
injective source-support-minimal forbidden EHN witness.

For a real full native free amalgam of two F-free sides carrying the
same full original global canonical lift, this witness is automatically
injective on its entire common-root preimage. The verified
minimal-global-obstruction theorem then produces a genuine minimal
mixed geometric piece, with the native full function-closed separator.

This is an actual one-step handoff to the Track C geometric descent.
It does NOT prove that either test-cover premise follows from
connectedness or regularity, and it does NOT prove positive-rank
successors, the terminal minimizer contradiction, or strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the ORIGINAL printed image-closure axiom, source-irreducible
test coverage for BOTH kinds of old inputs selects an ACTUAL
globally source-support-minimal, injective forbidden witness.
For the ACTUAL full free amalgam of matching canonical maximal
lifts, the verified root-injective obstruction lemma then selects
a genuinely MIXED positive-width geometric piece of MINIMAL
nonroot source size. No independent root-injectivity hypothesis
is needed; the explicit input-test covers supply it indirectly.

The cover hypotheses are independent of the 2019 connectedness
and forbidden-family image-closure conditions. -/
theorem exists_injectiveMinimalForbiddenWitness_with_minimalMixedPiece_of_inputCovers
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W),
      F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    (hFunctionInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src)
    (hRelationInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → RelationInputTuplesCoveredByIrreducibleTests Src)
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
      Function.Injective w.toTarget ∧
      (∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
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
  obtain ⟨w, hInjective, hMin⟩ :=
    exists_injectiveMinimalForbiddenEHNWitness_of_bothInputCovers
      F hFiniteF hImage hFunctionInputCover hRelationInputCover
      Target (fullFreeLeftExclusiveTarget iLeft jLeft) hExists
  have hRootInjOn : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) := by
    intro x _ y _ hEqual
    exact hInjective hEqual
  obtain ⟨P, hSmallest⟩ :=
    minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon
      hAvoidLeft hAvoidRight w hMin hRootInjOn
  exact ⟨w, hInjective, hMin, P, hSmallest⟩

end AllThoseRamseyClasses.Lifts
