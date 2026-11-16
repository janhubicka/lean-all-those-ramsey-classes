import AllThoseRamseyClasses.Lifts.EHNPrintedTupleAllSupportReplacement
import AllThoseRamseyClasses.Lifts.Claim2InjectiveLexActualTradeoff
import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn

/-!
# Original printed tuple-image closure: SAME-WITNESS lex and mixed piece

The printed forbidden-family image clause is weaker than genuine
vertex-surjective EHN image closure: the image is required to
CONTAIN a forbidden full substructure, not itself to be forbidden.

A chosen global (A-source,B-source)-lex-minimum forbidden EHN
witness with function-closed actual target range and OLD
tuple-surjective map into that FULL induced range still has
ONE injective forbidden replacement preserving BOTH global
minimalities. Source preimages of one full forbidden subimage
yield simultaneous support inequalities in every target region.

The verified original global-minimal mixed-piece theorem then
constructs a genuine smallest positive-width mixed geometric
piece of the SAME injective source/map. The verified all-width
successor makes a REAL B-decreasing forbidden source in the
same actual target. Necessarily it has strictly higher A
exclusive SOURCE count than the original lex minimum.

The two source-local hypotheses (range closed, OLD
tuple-surjective induced range) remain EXPLICIT. They are
not automatic from the printed family image clause.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the exact printed image clause, a SINGLE chosen original
globally lex-minimal forbidden weak EHN source whose actual range
is function-closed and tuple-surjective can be replaced by ONE
injective lex-minimal forbidden native witness carrying its own
smallest genuine positive-width mixed geometric separator.

The image-to-target map need not have been injective, and the
forbidden full subimage need NOT equal the whole induced range. -/
theorem exists_selectedPrintedTupleLex_injective_minimalMixed
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
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
    (hSelectedPrintedLex :
      ∃ (w : ForbiddenEHNWitness F Target)
        (hClosed : Target.IsClosed (Set.range w.toTarget)),
        OriginalPartialTupleSurjective
          w.source (Target.induce (Set.range w.toTarget) hClosed)
          (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
            Set.range w.toTarget)) ∧
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
  obtain ⟨w, hClosed, hTuple, hOldA, hOldB⟩ :=
    hSelectedPrintedLex
  obtain ⟨v, hInjective, hNonIncrease⟩ :=
    forbiddenEHNWitness_injectiveReplacement_allSupport_of_printedTupleRange
      F hFiniteF hImage Target w hClosed hTuple
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
    intro z hEq
    have hEqOld :
        z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) :=
      hEq.trans hEqualA
    exact (hNonIncrease (fullFreeRightExclusiveTarget iRight jRight)).trans
      (hOldB z hEqOld)
  have hRootInjOn : Set.InjOn v.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget) := by
    intro x _ y _ hEq
    exact hInjective hEq
  obtain ⟨P, hSmallest⟩ :=
    minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight
      v hMinA hRootInjOn
  exact ⟨v, hInjective, hMinA, hMinB, P, hSmallest⟩

/-- Same selected printed-tuple lex-minimum produces a GENUINE
second finite forbidden native EHN map into the SAME full
target whose B-exclusive SOURCE count is strictly LOWER and
whose A-exclusive SOURCE count is necessarily strictly HIGHER.

No stronger surjective-EHN family closure; no pretending that
the tuple-surjective image itself belongs to F; no A-neutrality
or minimality inheritance claimed for the flipped source. -/
theorem exists_selectedPrintedTupleLex_actualFlip_strictBA
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
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
    (hSelectedPrintedLex :
      ∃ (w : ForbiddenEHNWitness F Target)
        (hClosed : Target.IsClosed (Set.range w.toTarget)),
        OriginalPartialTupleSurjective
          w.source (Target.induce (Set.range w.toTarget) hClosed)
          (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
            Set.range w.toTarget)) ∧
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
    ∃ (v z : ForbiddenEHNWitness F Target),
      Function.Injective v.toTarget ∧
      z.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) <
      v.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) ∧
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) <
      z.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) := by
  obtain ⟨v, hvInj, hMinA, hMinB, P, hSmallest⟩ :=
    exists_selectedPrintedTupleLex_injective_minimalMixed
      F hFiniteF hImage hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight hSelectedPrintedLex
  obtain ⟨z, hStrictB, hStrictA⟩ :=
    claim2_injectiveLexMinimum_smallestMixed_hasStrictBAflip
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon v hvInj hMinA hMinB P hSmallest
  exact ⟨v, z, hvInj, hStrictB, hStrictA⟩

end AllThoseRamseyClasses.Lifts
