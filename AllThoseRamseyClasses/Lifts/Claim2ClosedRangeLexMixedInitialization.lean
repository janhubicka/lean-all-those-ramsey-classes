import AllThoseRamseyClasses.Lifts.Claim2ClosedRangeInjectiveLexMinimizer
import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn
import AllThoseRamseyClasses.Lifts.Claim2InjectiveMixedAllWidthsFlip
import AllThoseRamseyClasses.Lifts.Claim2SelectedOuterStrictGlobalB

/-!
# Corrected original Claim 2: one lex-minimal source, one genuine mixed piece

This is the missing SAME-WITNESS initialization for the corrected,
stronger vertex-surjective EHN-image-closed forbidden family.

The first theorem combines the verified injective global (A,B)-lex
minimum with the verified existence of a genuine smallest positive-width
mixed geometric separator.  The global minimality, injectivity and
geometric piece all belong to EXACTLY THE SAME original forbidden
native source-to-target weak EHN witness.

The second theorem applies the checked all-root-width geometric flip to
this witness: there exists an ACTUAL second forbidden native source
mapping weakly EHN into the same free target, with strictly smaller
GLOBAL B-exclusive SOURCE support.  Lexicographic minimality forces
the new total A-exclusive SOURCE support to be STRICTLY GREATER.

This is a conditional corrected-source initialization and structural
obstruction, NOT Claim 2 itself.  In particular, the actual flip does
not preserve the original A-minimum, and does not yield an iteration.
Source range closedness is required for EVERY forbidden witness mapping
to the FIXED target; it is automatic for function-free relations but
NOT for general functions.  Likewise vertex-surjective EHN image
closure is strictly stronger than printed tuple-image closure.
The 2019 numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under genuine vertex-surjective EHN image closure and closed ranges,
an actual full free amalgam of two F-free sides with a common original
global canonical lift has ONE injective, lexicographically minimal
forbidden native source carrying a TRUE smallest mixed geometric piece.
No mixed piece or root-injectivity is postulated separately. -/
theorem exists_closedRange_injectiveLex_minimalMixedPiece
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
    (hClosedAll : ∀ w : ForbiddenEHNWitness F Target,
      Target.IsClosed (Set.range w.toTarget)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      (∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      (∀ w : ForbiddenEHNWitness F Target,
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) =
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) →
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        w.sourceSupportCount
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
  obtain ⟨v, hvInjective, hMinA, hMinB⟩ :=
    exists_injective_global_lex_minimum_forbiddenEHN_of_closedRange
      F hFiniteF hImageClosed Target
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      (fullFreeRightExclusiveTarget iRight jRight)
      hNonempty hClosedAll
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

/-- Fully source-level corrected Claim 2 initial flip: for ONE
injective, lex-minimal original forbidden witness with a genuine
smallest mixed separator, the checked all-width successor gives
a REAL different finite forbidden source with GLOBAL B count
strictly decreased and GLOBAL A count strictly increased.

The latter is a THEOREM forced by the lex minimum (not an assumed
A-neutrality of the selected Q).  The original canonical/global
root information is used internally by the actual all-width flip;
the output records the strict global support tradeoff. -/
theorem exists_closedRange_lexMinimum_actualFlip_strictGlobalBAtradeoff
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
    (hClosedAll : ∀ w : ForbiddenEHNWitness F Target,
      Target.IsClosed (Set.range w.toTarget)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      (∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      (∀ w : ForbiddenEHNWitness F Target,
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) =
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) →
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight)) ∧
      ∃ w : ForbiddenEHNWitness F Target,
        w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) <
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ∧
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) <
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) := by
  classical
  obtain ⟨v, hvInjective, hMinA, hMinB, P, hPminimal⟩ :=
    exists_closedRange_injectiveLex_minimalMixedPiece
      F hFiniteF hImageClosed hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight hNonempty hClosedAll
  have hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {x : v.Carrier //
        v.toTarget x ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {y : W //
        g y ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    intro W New hNew g hg
    let w : ForbiddenEHNWitness F Target := {
      Carrier := W
      finiteCarrier := hFiniteF New hNew
      source := New
      forbidden := hNew
      toTarget := g
      homEmbedding := hg
    }
    exact hMinA w
  obtain ⟨a, m, d, hm, hProper,
      W, New, hNew, hFiniteNew, g, newOuter,
      hHom, hRootCoords, hSymbol, hLocalB, hExterior, hAnchor⟩ :=
    claim2_originalAMinimal_injective_mixed_allWidths_hasActualFlip
      F hFiniteF hConnected
      v.source v.finiteCarrier v.forbidden Target
      v.toTarget v.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon P hPminimal hvInjective hAMinimal
  let w : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteNew
    source := New
    forbidden := hNew
    toTarget := g
    homEmbedding := hHom
  }
  have hStrictB :
      w.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) <
      v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) := by
    exact finiteSource_strict_global_active_of_inside_and_exterior
      v.finiteCarrier hFiniteNew
      (geometricPieceVertices v.source P.data)
      (geometricPieceVertices New newOuter)
      v.toTarget g (fullFreeRightExclusiveTarget iRight jRight)
      hLocalB (hExterior (fullFreeRightExclusiveTarget iRight jRight))
  have hStrictA :
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) <
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    rcases lt_or_eq_of_le (hMinA w) with hLess | hEq
    · exact hLess
    · have hBLower := hMinB w hEq.symm
      exact False.elim ((Nat.not_lt_of_ge hBLower) hStrictB)
  exact ⟨v, hvInjective, hMinA, hMinB, w, hStrictB, hStrictA⟩

end AllThoseRamseyClasses.Lifts
