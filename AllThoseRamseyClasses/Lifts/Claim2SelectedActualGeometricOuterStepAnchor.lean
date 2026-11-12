import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.Claim2ActualOuterStatePersistence

/-!
# One genuine selected-Q flip preserves BOTH exterior source counts and A anchor

The existing same-Q full-native source replacement already returns
an exact all-target SOURCE-support conservation theorem outside the
old/new actual geometric outer pieces, plus an exact carrier equality.
The previously checked anchor-transport lemma turns those exact
source certificates into a surviving A-exclusive SOURCE vertex INSIDE
the new actual outer geometric piece.

This module combines the two without a new glued source, any
minimization of A-exclusive source support, or target-image counting.
The result is one witness with strict B-only SOURCE rank decrease,
unchanged outer ordered target root, same global canonical symbol,
invariant exterior source support counts, and an actual A-only anchor.

The theorem is conditional on an already eligible one-sided geometric
inner piece and exact inner root image injectivity. It does NOT prove
the existence of such an inner piece at every positive B-rank state,
nor injectivity of the entire new seam.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A real A-only source anchor survives an eligible genuine
same-Q right-to-left source replacement; the *same witness* also
preserves every exterior source-support count and strictly decreases
local B-only SOURCE rank. No original A-minimality is assumed. -/
theorem geometricGlobalRightFlip_actualOuterPiece_withExteriorAndAnchor
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (anchor : V)
    (hAnchorOuter : anchor ∈ geometricPieceVertices Old outer)
    (hAnchorA : f anchor ∈ fullFreeLeftExclusiveTarget iLeft jLeft) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (hFiniteNew : Finite V') (flip : V' → UT)
      (newOuter : GeometricFunctionalPieceData New n),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ i : Fin n, flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) ∧
      ∃ anew : V',
        anew ∈ geometricPieceVertices New newOuter ∧
        flip anew = f anchor ∧
        flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
  obtain ⟨V', New, hNew, Q, _hSelected,
      iQ, iE, _hNewFree, flip, hFlip,
      hFiniteNew, newOuter, _hRoot, hEAgree,
      _hRootCoords, hCarrier, hTargetCoords,
      hSymbol, hRank, hExterior, _hProfile⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExteriorAndAllTests
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  have hInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      f z ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro z hz hzA
    exact hInnerNoLeft z hz
      ((weakFreeLeftPart_iff_targetExclusive iLeft jLeft f z).mpr hzA)
  obtain ⟨anew, haOuterNew, haSame, haNewA⟩ :=
    geometricOuterAnchor_survives_selectedInnerFlip
      Old outer inner Q New iQ iE newOuter hCarrier
      f flip hEAgree
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      anchor hAnchorOuter hAnchorA hInnerNoA
  exact ⟨V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hTargetCoords, hSymbol, hRank, hExterior,
    anew, haOuterNew, haSame, haNewA⟩

end AllThoseRamseyClasses.Lifts
