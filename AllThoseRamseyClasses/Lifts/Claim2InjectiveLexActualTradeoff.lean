import AllThoseRamseyClasses.Lifts.Claim2SelectedClosedLexActualTradeoff

/-!
# Original Claim 2 global support tradeoff: image-closure-free core

The ACTUAL geometric all-width positive-B native flip requires only
a genuinely injective global A-minimum original forbidden EHN
source and an actual smallest mixed positive-width source piece;
no image-closure assumption occurs in the geometric successor.

If the original is also globally B-minimal among A-minima, exact
finite SOURCE inside/outside counting gives a second actual
F-forbidden EHN witness in the SAME full free-amalgam target with
strictly smaller total B-exclusive SOURCE support. Its A-exclusive
SOURCE support must strictly increase, or the original global lex
minimum would be contradicted.

Extracting this lemma separates the geometric/proof-control step
from alternative ways of selecting the ORIGINAL injective lex
minimum (strong EHN image closure, or printed tuple image closure
plus protected source input tuples). Neither A-minimality
inheritance nor unrestricted strong amalgamation is claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- From one ACTUAL injective original (A,B)-lex-minimal forbidden
EHN source and its smallest mixed geometric source piece, there
is ONE real B-decreasing forbidden EHN replacement at higher A
source cost. No image-closure or range-closedness hypotheses
are used AFTER the input witness has been selected. -/
theorem claim2_injectiveLexMinimum_smallestMixed_hasStrictBAflip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
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
    (v : ForbiddenEHNWitness F Target)
    (hInjective : Function.Injective v.toTarget)
    (hMinA : ∀ z : ForbiddenEHNWitness F Target,
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hMinB : ∀ z : ForbiddenEHNWitness F Target,
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) →
      v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ≤
      z.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight))
    (P : MixedGeometricPiece v.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) v.toTarget))
    (hSmallest : ∀ Q : MixedGeometricPiece v.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) v.toTarget),
      P.nonrootCount ≤ Q.nonrootCount) :
    ∃ z : ForbiddenEHNWitness F Target,
      z.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) <
      v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ∧
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) <
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
  classical
  have hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {x : v.Carrier //
        v.toTarget x ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {y : W //
        g y ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    intro W New hNew g hg
    let z : ForbiddenEHNWitness F Target := {
      Carrier := W
      finiteCarrier := hFiniteF New hNew
      source := New
      forbidden := hNew
      toTarget := g
      homEmbedding := hg
    }
    exact hMinA z
  obtain ⟨a, m, d, hm, hProper,
      W, New, hNew, hFiniteNew, g, newOuter,
      hHom, hRootCoords, hSymbol, hLocalB, hExterior, hAnchor⟩ :=
    claim2_originalAMinimal_injective_mixed_allWidths_hasActualFlip
      F hFiniteF hConnected
      v.source v.finiteCarrier v.forbidden Target
      v.toTarget v.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon P hSmallest hInjective hAMinimal
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
  exact ⟨z, hStrictB, hStrictA⟩

end AllThoseRamseyClasses.Lifts
