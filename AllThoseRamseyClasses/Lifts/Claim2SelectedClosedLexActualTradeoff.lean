import AllThoseRamseyClasses.Lifts.Claim2SelectedClosedLexMixedInitialization

/-!
# Actual all-width original-source flip from just one closed lex minimum

A globally lex-minimal ORIGINAL forbidden EHN source with its OWN
function-closed actual target range can be injectivized under strong
vertex-surjective EHN image closure.  The same new injective minimum
contains a true smallest mixed geometric source piece, and the already
verified all-width successor gives a real forbidden replacement.

Global B-exclusive SOURCE cardinality strictly decreases, and by
the starting global (A,B)-lex minimum, global A-exclusive SOURCE
cardinality strictly increases.  No all-witness range-closedness
assumption is needed for THIS statement.

This supports corrected Claim 2 initialization but does not prove
A-neutral selected Q, induction, or the printed weaker theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the LOCAL selected-lex-minimum closed-range hypothesis
(and stronger genuine vertex-surjective EHN closure of F), the SAME
chosen injective minimal forbidden source has an ACTUAL native
all-width B-decreasing forbidden replacement.  The new SOURCE
necessarily pays strictly positive GLOBAL A-exclusive support.

No hypothesis that all forbidden maps have function-closed ranges;
no assumed initial mixed piece or source-root injection. -/
theorem exists_selectedClosedLex_actualFlip_strictGlobalBAtradeoff
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
      ∃ z : ForbiddenEHNWitness F Target,
        z.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) <
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ∧
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) <
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) := by
  classical
  obtain ⟨v, hvInjective, hMinA, hMinB, P, hPminimal⟩ :=
    exists_selectedClosedLex_injectiveMin_with_minimalMixedPiece
      F hFiniteF hImageClosed hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight hSelectedClosedLex
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
  let z : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteNew
    source := New
    forbidden := hNew
    toTarget := g
    homEmbedding := hHom
  }
  have hStrictB :
      z.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) <
      v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) := by
    exact finiteSource_strict_global_active_of_inside_and_exterior
      v.finiteCarrier hFiniteNew
      (geometricPieceVertices v.source P.data)
      (geometricPieceVertices New newOuter)
      v.toTarget g (fullFreeRightExclusiveTarget iRight jRight)
      hLocalB (hExterior (fullFreeRightExclusiveTarget iRight jRight))
  have hStrictA :
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) <
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    rcases lt_or_eq_of_le (hMinA z) with hLess | hEq
    · exact hLess
    · have hBLower := hMinB z hEq.symm
      exact False.elim ((Nat.not_lt_of_ge hBLower) hStrictB)
  exact ⟨v, hvInjective, hMinA, hMinB, z, hStrictB, hStrictA⟩

end AllThoseRamseyClasses.Lifts
