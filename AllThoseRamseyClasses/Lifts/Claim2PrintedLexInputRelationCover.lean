import AllThoseRamseyClasses.Lifts.Claim2PrintedTupleLexInitialization
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import AllThoseRamseyClasses.Lifts.Claim2GlobalLexSourceMinimizer

/-!
# Printed image closure: the chosen original lex-minimum input tests

The exact original 2019 tuple-surjective forbidden-image closure
is enough for the same-witness lex-minimizer/positive-rank
geometric source construction IF the chosen original global
lex-minimum has two additional SOURCE-LOCAL certificates:

1. full irreducible source tests protect all native function
   INPUT tuples, yielding exact full function fibres and a
   genuinely function-closed target image;
2. each positive target OLD relation on the actual source
   image range has a positive source-relation tuple preimage.

These imply tuple surjectivity into the actual FULL induced
range, so the paper-shaped image clause contains a full
forbidden substructure. The same replacement bounds ALL target
region source-support counts and thus remains global lex-minimal.

The second theorem begins with any forbidden weak EHN witness,
selects an original global lex minimum, and assumes the local
input certificates for lex minima (NOT arbitrary nonminimal maps).

Both tests are explicit. In particular, general connectedness,
regularity and the printed image clause are NOT shown to imply
the relation-side tuple certificate. Neither theorem proves
unrestricted 2019 Claim 2 or strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Printed tuple-image closure, plus FUNCTION input tests and
ACTUAL positive relation tuple preimages on ONE chosen original
global (A,B)-lex minimum, suffices for a genuine injective
original lex minimum, minimal mixed piece, and real forbidden
B-down/A-up source successor in the SAME full target.

The chosen source may be noninjective. No assumption that every
forbidden map has closed range or source input coverage. -/
theorem exists_printedSelectedLexInputRelation_actualFlip_strictBA
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
    (hSelectedLexCovers :
      ∃ w : ForbiddenEHNWitness F Target,
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
            (fullFreeRightExclusiveTarget iRight jRight)) ∧
        FunctionInputTuplesCoveredByIrreducibleTests w.source ∧
        SourceRelationTuplesCoveredOnRange
          w.source Target w.toTarget) :
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
  obtain ⟨w, hMinA, hMinB, hInput, hRelation⟩ :=
    hSelectedLexCovers
  let hClosed : Target.IsClosed (Set.range w.toTarget) :=
    ehn_range_isClosed_of_irreducibleInputCover
      w.source Target w.toTarget w.homEmbedding hInput
  have hTuple : OriginalPartialTupleSurjective
      w.source (Target.induce (Set.range w.toTarget) hClosed)
      (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
        Set.range w.toTarget)) :=
    ehn_actualInducedRange_tupleSurjective_of_inputTests_and_relationCover
      w.source Target w.toTarget w.homEmbedding
      hInput hRelation
  have hSelectedPrintedLex :
      ∃ (x : ForbiddenEHNWitness F Target)
        (hXClosed : Target.IsClosed (Set.range x.toTarget)),
        OriginalPartialTupleSurjective
          x.source (Target.induce (Set.range x.toTarget) hXClosed)
          (fun y => (⟨x.toTarget y, ⟨y, rfl⟩⟩ :
            Set.range x.toTarget)) ∧
        (∀ z : ForbiddenEHNWitness F Target,
          x.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
        (∀ z : ForbiddenEHNWitness F Target,
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) =
          x.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) →
          x.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight) ≤
          z.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight)) :=
    ⟨w, hClosed, hTuple, hMinA, hMinB⟩
  exact exists_selectedPrintedTupleLex_actualFlip_strictBA
    F hFiniteF hImage hConnected
    Target Left Right jLeft jRight X iLeft iRight
    hFree hCommon hAvoidLeft hAvoidRight hSelectedPrintedLex

/-- From ANY existing original F-forbidden weak EHN source,
take a GLOBAL original (A,B)-lex minimum. If EACH lex-minimal
source possesses its OWN full irreducible function-input test
coverage and ACTUAL positive relation tuple preimage
certificate, then the printed image clause suffices for a
real same-target native source successor with B strictly
decreased and A strictly increased.

No covers are required on nonminimum source witnesses; covers
for the chosen minimum are explicitly assumed, not inferred
from connectedness or image closure. -/
theorem exists_printedLexInputRelation_covers_actualFlip_strictBA
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
    (hNonempty : Nonempty (ForbiddenEHNWitness F Target))
    (hLexInputCover :
      ∀ w : ForbiddenEHNWitness F Target,
        (∀ z : ForbiddenEHNWitness F Target,
          w.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft)) →
        (∀ z : ForbiddenEHNWitness F Target,
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) =
          w.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) →
          w.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight) ≤
          z.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight)) →
        FunctionInputTuplesCoveredByIrreducibleTests w.source)
    (hLexRelationCover :
      ∀ w : ForbiddenEHNWitness F Target,
        (∀ z : ForbiddenEHNWitness F Target,
          w.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft)) →
        (∀ z : ForbiddenEHNWitness F Target,
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) =
          w.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) →
          w.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight) ≤
          z.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight)) →
        SourceRelationTuplesCoveredOnRange
          w.source Target w.toTarget) :
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
  obtain ⟨initial⟩ := hNonempty
  obtain ⟨W, New, hNew, hFiniteNew, g, hg,
      hMinA, hMinB⟩ :=
    exists_global_lex_minimum_weakForbiddenSource_support
      F hFiniteF Target initial.source initial.forbidden
      initial.toTarget initial.homEmbedding
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      (fullFreeRightExclusiveTarget iRight jRight)
  let w : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteNew
    source := New
    forbidden := hNew
    toTarget := g
    homEmbedding := hg
  }
  have hOldA : ∀ z : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro z
    exact hMinA z.source z.forbidden z.toTarget z.homEmbedding
  have hOldB : ∀ z : ForbiddenEHNWitness F Target,
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) →
      w.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ≤
      z.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) := by
    intro z hEqA
    exact hMinB z.source z.forbidden z.toTarget z.homEmbedding hEqA
  have hSelectedLexCovers :
      ∃ x : ForbiddenEHNWitness F Target,
        (∀ z : ForbiddenEHNWitness F Target,
          x.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
        (∀ z : ForbiddenEHNWitness F Target,
          z.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) =
          x.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) →
          x.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight) ≤
          z.sourceSupportCount
            (fullFreeRightExclusiveTarget iRight jRight)) ∧
        FunctionInputTuplesCoveredByIrreducibleTests x.source ∧
        SourceRelationTuplesCoveredOnRange
          x.source Target x.toTarget :=
    ⟨w, hOldA, hOldB,
      hLexInputCover w hOldA hOldB,
      hLexRelationCover w hOldA hOldB⟩
  exact exists_printedSelectedLexInputRelation_actualFlip_strictBA
    F hFiniteF hImage hConnected
    Target Left Right jLeft jRight X iLeft iRight
    hFree hCommon hAvoidLeft hAvoidRight hSelectedLexCovers

end AllThoseRamseyClasses.Lifts
