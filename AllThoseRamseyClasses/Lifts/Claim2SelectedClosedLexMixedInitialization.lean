import AllThoseRamseyClasses.Lifts.Claim2ClosedRangeLexMixedInitialization

/-!
# Only the chosen original lex-minimal forbidden source needs closed range

The previously verified injectivization works for ONE ACTUAL
selected forbidden source whose full target range is function closed.
The stronger first endpoint in
`Claim2ClosedRangeLexMixedInitialization` assumes this for every
forbidden witness mapping into the fixed full target.

Here we lower that to the existence of just ONE globally lex-minimal
(A-exclusive SOURCE, B-exclusive SOURCE) original forbidden EHN map
whose range is closed.  The injective replacement cannot increase
source support in ANY target subset, so it remains globally lex-minimal.
Consequently the full ORIGINAL mixed-piece existence argument still
applies on exactly that injective replacement.

This improves the logical dependency but does not derive range
closedness from the weaker printed tuple-image closure. In particular,
closedness of the chosen minimum still requires its own input
coverage proof or an independent class assumption.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A SINGLE actual original lexicographically minimal forbidden
weak EHN witness with a truly closed target range suffices to get a
possibly different INJECTIVE lex minimum and its smallest genuine
mixed positive-width geometric separator in the SAME new source.

No global assumption that EVERY forbidden weak map has closed range.
Neither the mixed piece nor initial target-root injectivity is assumed. -/
theorem exists_selectedClosedLex_injectiveMin_with_minimalMixedPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hImageClosed :
      ∀ {W Z : Type}
        (Src : Structure L W) (Dst : Structure L Z)
        (q : W → Z),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
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
    (hSelectedClosedLex :
      ∃ w : ForbiddenEHNWitness F Target,
        Target.IsClosed (Set.range w.toTarget) ∧
        (∀ z : ForbiddenEHNWitness F Target,
          w.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
        (∀ z : ForbiddenEHNWitness F Target,
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) =
          w.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) →
          w.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight) ≤
          z.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight))) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      (∀ z : ForbiddenEHNWitness F Target,
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      (∀ z : ForbiddenEHNWitness F Target,
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) =
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) →
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        z.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight)) ∧
      ∃ P : MixedGeometricPiece v.source
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
        (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
        (weakFreeRightPart (sL := iLeft) (iL := jLeft)
          (iR := jRight) v.toTarget),
        ∀ Q : MixedGeometricPiece v.source
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
          (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
          (weakFreeRightPart (sL := iLeft) (iL := jLeft)
            (iR := jRight) v.toTarget),
          P.nonrootCount ≤ Q.nonrootCount := by
  obtain ⟨w, hClosed, hOldA, hOldB⟩ := hSelectedClosedLex
  obtain ⟨v, hvInjective, hNonIncrease⟩ :=
    forbiddenEHNWitness_injectiveReplacement_allSupport_of_closedRange
      F hImageClosed Target w hClosed
  have hMinA : ∀ z : ForbiddenEHNWitness F Target,
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro z
    exact (hNonIncrease (fullFreeLeftExclusiveTarget iLeft jLeft)).trans
      (hOldA z)
  have hEqualA :
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) :=
    Nat.le_antisymm
      (hNonIncrease (fullFreeLeftExclusiveTarget iLeft jLeft))
      (hOldA v)
  have hMinB : ∀ z : ForbiddenEHNWitness F Target,
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) →
      v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ≤
      z.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) := by
    intro z hz
    have hzOld :
        z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) :=
      hz.trans hEqualA
    exact (hNonIncrease (fullFreeRightExclusiveTarget iRight jRight)).trans
      (hOldB z hzOld)
  have hRootInjOn : Set.InjOn v.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget) := by
    intro x _ y _ hEq
    exact hvInjective hEq
  obtain ⟨P, hSmallest⟩ :=
    minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight
      v hMinA hRootInjOn
  exact ⟨v, hvInjective, hMinA, hMinB, P, hSmallest⟩

end AllThoseRamseyClasses.Lifts
