import AllThoseRamseyClasses.Lifts.Claim2AllWidthsPositiveRankFlip

/-!
# Injective original minimal mixed source: actual all-width B-decreasing flip

The corrected image-closure route can yield an INJECTIVE finite
original forbidden source weak EHN map into the fixed full target.
Then the arbitrary boundary-injection premise of the VERIFIED
all-width positive-B Claim 2 theorem is AUTOMATIC for EVERY
full function-generated source boundary.

A genuine A/B-mixed geometric source P itself supplies:
* an actual A-exclusive SOURCE anchor in its chosen component;
* an actual B-exclusive SOURCE vertex in the SAME component;
* positive local B-only SOURCE Nat.card from that vertex.

Therefore an injective F-forbidden original witness that is
globally A-source-minimal, with P a globally smallest mixed
geometric piece, admits the one-step genuine B-exclusive
SOURCE-rank-decreasing selected-Q replacement, irrespective
of P's root width, without a separately assumed boundary-
injectivity certificate or B-rank positivity.

This does not infer the source-map injectivity from the weaker
printed 2019 tuple-surjective image closure. The independent
closed-range and vertex-surjective image-closure repair is in
draft #1236. Global A-source minimality may NOT survive the
B-to-A flip, so this remains a one-step theorem rather
than an unrestricted contradiction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An INJECTIVE globally A-source-minimum F-forbidden EHN
witness with a globally smallest genuinely mixed geometric
piece automatically satisfies the positive B-support and
complete local B-active generated-boundary injection
assumptions of the checked all-width Claim 2 successor.
The selected Q and native new source witness are REAL;
no extra root-tuple image-injectivity assumption. -/
theorem claim2_originalAMinimal_injective_mixed_allWidths_hasActualFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (P : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f))
    (hMinimal : ∀ Q : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f),
      P.nonrootCount ≤ Q.nonrootCount)
    (hInjective : Function.Injective f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    ∃ a : V,
      ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P.data ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New P.width),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin P.width,
          flip (newOuter.roots i) = f (P.data.roots i)) ∧
        geometricGlobalPieceSymbol F Source
          hFinite hForbidden P.data P.positive =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter P.positive ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Source P.data ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Source P.data ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft) := by
  classical
  letI : Finite V := hFinite
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨a, haComp, haA⟩ := P.left_mixed
  obtain ⟨b, hbComp, hbB⟩ := P.right_mixed
  have hTargetAgree : ∀ r : UX,
      jRight (iRight r) = jLeft (iLeft r) := by
    intro r
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hbSwapped :
      b ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hbB.1, ?_⟩
    intro hRootR
    obtain ⟨r, hr⟩ := hRootR
    apply hbB.2
    exact ⟨r, (hTargetAgree r).symm.trans hr⟩
  have hbTarget :
      f b ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive
      iRight jRight f b).mp hbSwapped
  have hPositiveB :
      0 < Nat.card {v : V //
        v ∈ geometricPieceVertices Source P.data ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    have hNonempty :
        Nonempty {v : V //
          v ∈ geometricPieceVertices Source P.data ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
      ⟨⟨b, Or.inr hbComp, hbTarget⟩⟩
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hNonempty
  have hLocalB : ∀
      (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
      x.1 ∈ geometricPieceVertices Source P.data →
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f →
      Set.InjOn f
        (Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))) := by
    intro _x _hxOuter _hxRight y _hy z _hz hyz
    exact hInjective hyz
  refine ⟨a, ?_⟩
  exact claim2_originalAMinimal_allWidths_positiveB_hasActualFlip
    F hFiniteF hConnected
    Source hFinite hForbidden Target f hf
    Left Right jLeft jRight X iLeft iRight hFree hCommon
    P hMinimal a (Or.inr haComp) haA hPositiveB hLocalB hAMinimal

/-- A nonempty collection of actual mixed minimal-separator
SOURCE pieces in an INJECTIVE globally A-minimal forbidden
weak-map witness suffices: the verified finite-source
smallest-nonroot-piece selection chooses P, and the previous
theorem constructs the real B-decreasing same-symbol successor.

No independent choice of source/weak map is made; the only
choice is the smallest mixed source piece INSIDE that same
original source. -/
theorem claim2_originalAMinimal_injective_nonemptyMixed_allWidths_hasActualFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hExists : Nonempty (MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f)))
    (hInjective : Function.Injective f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    ∃ P : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f),
      ∃ a : V,
      ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P.data ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New P.width),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin P.width,
          flip (newOuter.roots i) = f (P.data.roots i)) ∧
        geometricGlobalPieceSymbol F Source
          hFinite hForbidden P.data P.positive =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter P.positive ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Source P.data ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Source P.data ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft) := by
  classical
  letI : Finite V := hFinite
  obtain ⟨P, hMin⟩ :=
    exists_minimalMixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f) hExists
  refine ⟨P, ?_⟩
  exact claim2_originalAMinimal_injective_mixed_allWidths_hasActualFlip
    F hFiniteF hConnected Source hFinite hForbidden
    Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    P hMin hInjective hAMinimal



/-!
## Global lexicographic accounting gate

The actual all-width successor above lowers B support INSIDE the selected
outer piece and preserves every exterior source count.  That does NOT by
itself improve the global lexicographic pair: a flip may create additional
A-exclusive source support inside the replaced piece.  The next two
elementary lemmas isolate exactly the additional non-growth hypothesis
required for a legitimate contradiction.  They are deliberately
conditional, and do not assert that the geometric flip supplies it.
-/

/-- The numerical accounting step from local A non-growth and strict
local B decrease to a strict global lexicographic improvement, when
both exterior support counts are conserved. -/
theorem claim2_lexSupport_improves_of_A_nonGrowth_B_strict
    (aExterior bExterior aOld aNew bOld bNew : ℕ)
    (hANonGrowth : aNew ≤ aOld)
    (hBDecrease : bNew < bOld) :
    aExterior + aNew < aExterior + aOld ∨
      (aExterior + aNew = aExterior + aOld ∧
       bExterior + bNew < bExterior + bOld) := by
  omega

/-- Thus a lexicographically minimal original witness forbids an
A-non-growing flip with strict B decrease.  The all-width geometric
successor proves the latter, but NOT the former. -/
theorem claim2_lexSupport_impossible_of_minimal_and_A_nonGrowth
    (aExterior bExterior aOld aNew bOld bNew : ℕ)
    (hGlobalAMinimal : aExterior + aOld ≤ aExterior + aNew)
    (hGlobalBTieMinimal :
      aExterior + aOld = aExterior + aNew →
      bExterior + bOld ≤ bExterior + bNew)
    (hANonGrowth : aNew ≤ aOld)
    (hBDecrease : bNew < bOld) : False := by
  rcases claim2_lexSupport_improves_of_A_nonGrowth_B_strict
      aExterior bExterior aOld aNew bOld bNew
      hANonGrowth hBDecrease with hStrictA | ⟨hEqA, hStrictB⟩
  · exact (Nat.not_lt_of_ge hGlobalAMinimal) hStrictA
  · exact (Nat.not_lt_of_ge (hGlobalBTieMinimal hEqA.symm)) hStrictB


/-- The converse accounting obstruction: for a GLOBAL lexicographic
minimum with exactly conserved exterior counts, ANY strictly
B-decreasing local replacement must have STRICTLY MORE local
A-exclusive SOURCE support.  In particular, the candidate
B-to-A flip cannot be iterated while retaining the same A-minimum,
unless a different surgery changes the accounting. -/
theorem claim2_lexMinimal_strict_A_growth_of_local_B_decrease
    (aExterior bExterior aOld aNew bOld bNew : ℕ)
    (hGlobalAMinimal : aExterior + aOld ≤ aExterior + aNew)
    (hGlobalBTieMinimal :
      aExterior + aOld = aExterior + aNew →
      bExterior + bOld ≤ bExterior + bNew)
    (hBDecrease : bNew < bOld) :
    aOld < aNew := by
  by_contra hNotGrowth
  have hANonGrowth : aNew ≤ aOld := Nat.le_of_not_gt hNotGrowth
  exact claim2_lexSupport_impossible_of_minimal_and_A_nonGrowth
    aExterior bExterior aOld aNew bOld bNew
    hGlobalAMinimal hGlobalBTieMinimal hANonGrowth hBDecrease

/-- The exact numerical support cost of a B-decreasing flip is
at least one new A-exclusive SOURCE vertex when the starting
witness minimizes the global lexicographic pair. -/
theorem claim2_lexMinimal_A_cost_at_least_one
    (aExterior bExterior aOld aNew bOld bNew : ℕ)
    (hGlobalAMinimal : aExterior + aOld ≤ aExterior + aNew)
    (hGlobalBTieMinimal :
      aExterior + aOld = aExterior + aNew →
      bExterior + bOld ≤ bExterior + bNew)
    (hBDecrease : bNew < bOld) :
    aOld + 1 ≤ aNew := by
  exact Nat.succ_le_iff.mpr
    (claim2_lexMinimal_strict_A_growth_of_local_B_decrease
      aExterior bExterior aOld aNew bOld bNew
      hGlobalAMinimal hGlobalBTieMinimal hBDecrease)


end AllThoseRamseyClasses.Lifts
