import AllThoseRamseyClasses.Lifts.Claim2SelectedClosedLexActualTradeoff
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre

/-!
# A concrete source-test interface for the selected lex-minimal range

For original native partial-function structures a weak EHN target
image need not be function closed.  The checked source-local
irreducible-function-input-cover lemma *does* close the actual
range of a weak EHN map.

Here choose one global lex-minimal original finite forbidden weak
EHN source. If every such chosen global lex-minimal source has
its native primitive function INPUT TUPLES covered by full irreducible
source tests, then the CHOSEN source's range is closed.  Apply the
same-witness selected-lex closed-range theorem to get one injective
lex-minimal mixed piece and a real B-down/A-up forbidden replacement.

This is a new conditional source-test-to-geometric initialization
bridge. The input-cover-for-minimizers property is EXPLICIT; neither
original printed image closure nor maximal canonical profiles
have been proved to supply it.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The existing original global lex selection, followed by its OWN
full irreducible function-input tests, produces one closed-range
original lex-minimal forbidden weak EHN witness. The assumption
concerns only globally lex-minimal SOURCE witnesses; arbitrary
nonminimal forbidden maps need not have closed range. -/
theorem exists_globalLex_forbiddenEHN_closedRange_of_lexInputCover
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UT : Type} (Target : Structure L UT)
    (AActive BActive : Set UT)
    (hNonempty : Nonempty (ForbiddenEHNWitness F Target))
    (hLexInputCover :
      ∀ w : ForbiddenEHNWitness F Target,
        (∀ z : ForbiddenEHNWitness F Target,
          w.sourceSupportCount AActive ≤
          z.sourceSupportCount AActive) →
        (∀ z : ForbiddenEHNWitness F Target,
          z.sourceSupportCount AActive =
          w.sourceSupportCount AActive →
          w.sourceSupportCount BActive ≤
          z.sourceSupportCount BActive) →
        FunctionInputTuplesCoveredByIrreducibleTests w.source) :
    ∃ w : ForbiddenEHNWitness F Target,
      Target.IsClosed (Set.range w.toTarget) ∧
      (∀ z : ForbiddenEHNWitness F Target,
        w.sourceSupportCount AActive ≤ z.sourceSupportCount AActive) ∧
      (∀ z : ForbiddenEHNWitness F Target,
        z.sourceSupportCount AActive =
        w.sourceSupportCount AActive →
        w.sourceSupportCount BActive ≤
        z.sourceSupportCount BActive) := by
  obtain ⟨initial⟩ := hNonempty
  obtain ⟨W, New, hNew, hFiniteNew, g, hg,
      hMinA, hMinB⟩ :=
    exists_global_lex_minimum_weakForbiddenSource_support
      F hFiniteF Target initial.source initial.forbidden
      initial.toTarget initial.homEmbedding AActive BActive
  let w : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteNew
    source := New
    forbidden := hNew
    toTarget := g
    homEmbedding := hg
  }
  have hOldA : ∀ z : ForbiddenEHNWitness F Target,
      w.sourceSupportCount AActive ≤
      z.sourceSupportCount AActive := by
    intro z
    exact hMinA z.source z.forbidden z.toTarget z.homEmbedding
  have hOldB : ∀ z : ForbiddenEHNWitness F Target,
      z.sourceSupportCount AActive = w.sourceSupportCount AActive →
      w.sourceSupportCount BActive ≤
      z.sourceSupportCount BActive := by
    intro z hEqA
    exact hMinB z.source z.forbidden z.toTarget z.homEmbedding hEqA
  have hInputCover :
      FunctionInputTuplesCoveredByIrreducibleTests w.source :=
    hLexInputCover w hOldA hOldB
  have hClosed : Target.IsClosed (Set.range w.toTarget) :=
    ehn_range_isClosed_of_irreducibleInputCover
      w.source Target w.toTarget w.homEmbedding hInputCover
  exact ⟨w, hClosed, hOldA, hOldB⟩

/-- Concrete functional input-test version of the selected-closed-lex
actual original-source B-to-A successor.  It starts with one arbitrary
nonempty forbidden EHN witness, chooses the original global
lex-minimum itself, establishes its range closedness using the exact
source-native irreducible input-test cover, and builds a real
B-decreasing forbidden replacement that necessarily pays positive
A-exclusive SOURCE cost.

This does NOT derive the selected-lex input-test cover hypothesis
from F's image closure or common canonical lift. -/
theorem exists_lexInputCovered_actualFlip_strictGlobalBAtradeoff
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
        FunctionInputTuplesCoveredByIrreducibleTests w.source) :
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
      ∃ z : ForbiddenEHNWitness F Target,
        z.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) <
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ∧
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) <
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) := by
  have hSelectedClosedLex :=
    exists_globalLex_forbiddenEHN_closedRange_of_lexInputCover
      F hFiniteF Target
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      (fullFreeRightExclusiveTarget iRight jRight)
      hNonempty hLexInputCover
  exact exists_selectedClosedLex_actualFlip_strictGlobalBAtradeoff
    F hFiniteF hImageClosed hConnected
    Target Left Right jLeft jRight X iLeft iRight
    hFree hCommon hAvoidLeft hAvoidRight hSelectedClosedLex

end AllThoseRamseyClasses.Lifts
