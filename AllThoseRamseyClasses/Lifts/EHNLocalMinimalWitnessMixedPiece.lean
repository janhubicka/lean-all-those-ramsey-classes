import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn

/-!
# Track D: source-local injectivization at ONE support-minimal witness

The existing Track D -> Track C handoff under the printed
tuple-surjective forbidden-image closure has been packaged under
GLOBAL source-test coverage assumptions for ALL forbidden structures.
That is stronger than this composition actually needs.

Choose ONE original finite forbidden EHN witness w of globally minimal
LEFT-exclusive SOURCE support in the ACTUAL target free amalgam.
Assume only (1) its own native function inputs have full irreducible
source tests and (2) its own positive target relation tuples on
the actual image range have positive source preimages. Then
its actual target range is function-closed, its source-to-range map
is original-partial tuple-surjective, and the printed family
image closure supplies an INJECTIVE replacement v with no larger
source support. Minimality of w makes v still minimal, and the
existing root-injective geometry yields a genuine smallest MIXED
piece for v.

The two source-local premises remain EXPLICIT. This theorem does NOT
claim that common maximal canonical lifts imply them. It is a
strictly weaker proof interface than whole-family test coverage, not
an unconditional original Section 3 strong AP result.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The original printed image closure and exactly ONE support-minimal
forbidden weak EHN witness w suffice to produce an ACTUAL
support-minimal INJECTIVE replacement and its smallest genuine
mixed geometric separator piece, provided only w's own
function inputs are protected by full irreducible source tests
and every positive target OLD relation on its range has an
actual source positive relation-tuple preimage.

These are local, independently named hypotheses, not global
forbidden-family source test covers. The target is the real
FULL native free amalgam of original global maximal lifts. -/
theorem minimalForbiddenWitness_localRangeReflection_yields_injectiveMinimalMixedPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W),
      F A → Finite W)
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
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ t : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hInputCover : FunctionInputTuplesCoveredByIrreducibleTests w.source)
    (hRelationRange : SourceRelationTuplesCoveredOnRange
      w.source Target w.toTarget) :
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
          P.nonrootCount ≤ Q.nonrootCount := by
  let hClosed : Target.IsClosed (Set.range w.toTarget) :=
    ehn_range_isClosed_of_irreducibleInputCover
      w.source Target w.toTarget w.homEmbedding hInputCover
  have hTuple : OriginalPartialTupleSurjective
      w.source (Target.induce (Set.range w.toTarget) hClosed)
      (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
        Set.range w.toTarget)) :=
    ehn_actualInducedRange_tupleSurjective_of_inputTests_and_relationCover
      w.source Target w.toTarget w.homEmbedding
      hInputCover hRelationRange
  obtain ⟨v, hInjective, hSupportBound⟩ :=
    forbiddenEHNWitness_injectiveReplacement_of_printedTupleRange
      F hFiniteF hImage Target
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      w hClosed hTuple
  have hMinimalV : ∀ t : ForbiddenEHNWitness F Target,
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro t
    exact hSupportBound.trans (hMin t)
  have hRootInjOn : Set.InjOn v.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget) := by
    intro a _ b _ hSame
    exact hInjective hSame
  obtain ⟨P, hSmallest⟩ :=
    minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight
      v hMinimalV hRootInjOn
  exact ⟨v, hInjective, hMinimalV, P, hSmallest⟩

end AllThoseRamseyClasses.Lifts
