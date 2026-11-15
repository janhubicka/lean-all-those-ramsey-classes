import AllThoseRamseyClasses.Lifts.Claim2SelectedOuterFullState
import Mathlib.Data.Set.Card

/-!
# Strict GLOBAL B-exclusive SOURCE decrease from exact geometric outer descent

The checked same-selected-Q actual native replacement provides a
strict decrease in B-exclusive SOURCE support INSIDE the new genuine
outer geometric minimal-separator piece, while conserving SOURCE
counts OUTSIDE for every fixed target set (in particular B-only).

On a finite old/new source, the total source active set is exactly
the disjoint union of inside and outside. Hence the new TOTAL
B-exclusive genuine SOURCE count is STRICTLY SMALLER.

This is stronger than the earlier local-rank result: it relates
the globally minimized number of B-active source vertices across
different forbidden original source carrier types.

It does NOT require original A-support neutrality or a globally
A-minimal original source; those are separate conditions for
a lexicographic (A,B) original-source minimization argument.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Count actual Active SOURCE vertices in a finite source by
partitioning into source vertices INSIDE a specified piece and
source vertices OUTSIDE. No injectivity of f is required. -/
theorem finiteSource_active_card_eq_inside_add_outside
    {V UT : Type}
    (hFinite : Finite V) (P : Set V)
    (f : V → UT) (Active : Set UT) :
    Nat.card {v : V // f v ∈ Active} =
      Nat.card {v : V // v ∈ P ∧ f v ∈ Active} +
      Nat.card {v : V // v ∉ P ∧ f v ∈ Active} := by
  classical
  letI : Finite V := hFinite
  let Inside : Set V := {v | v ∈ P ∧ f v ∈ Active}
  let Outside : Set V := {v | v ∉ P ∧ f v ∈ Active}
  have hPartition :
      {v : V | f v ∈ Active} = Inside ∪ Outside := by
    ext v
    constructor
    · intro hv
      by_cases hP : v ∈ P
      · exact Or.inl ⟨hP, hv⟩
      · exact Or.inr ⟨hP, hv⟩
    · intro h
      rcases h with hIn | hOut
      · exact hIn.2
      · exact hOut.2
  have hDisjoint : Disjoint Inside Outside := by
    apply Set.disjoint_left.mpr
    intro v hInside hOutside
    exact hOutside.1 hInside.1
  change Nat.card (↑({v : V | f v ∈ Active} : Set V)) =
    Nat.card (↑(Inside : Set V)) + Nat.card (↑(Outside : Set V))
  simp only [Nat.card_coe_set_eq]
  rw [hPartition, Set.ncard_union_eq hDisjoint]

/-- Strict inside-piece decrease of actual Active SOURCE vertices,
together with exact exterior SOURCE conservation, implies strict
decrease of TOTAL Active SOURCE support. Old/new source carrier
types may be different; no weak-map global injection. -/
theorem finiteSource_strict_global_active_of_inside_and_exterior
    {V W UT : Type}
    (hFiniteOld : Finite V) (hFiniteNew : Finite W)
    (OldPart : Set V) (NewPart : Set W)
    (f : V → UT) (flip : W → UT) (Active : Set UT)
    (hInside :
      Nat.card {w : W // w ∈ NewPart ∧ flip w ∈ Active} <
      Nat.card {v : V // v ∈ OldPart ∧ f v ∈ Active})
    (hOutside :
      Nat.card {w : W // w ∉ NewPart ∧ flip w ∈ Active} =
      Nat.card {v : V // v ∉ OldPart ∧ f v ∈ Active}) :
    Nat.card {w : W // flip w ∈ Active} <
      Nat.card {v : V // f v ∈ Active} := by
  have hOld := finiteSource_active_card_eq_inside_add_outside
    hFiniteOld OldPart f Active
  have hNew := finiteSource_active_card_eq_inside_add_outside
    hFiniteNew NewPart flip Active
  calc
    Nat.card {w : W // flip w ∈ Active} =
        Nat.card {w : W // w ∈ NewPart ∧ flip w ∈ Active} +
          Nat.card {w : W // w ∉ NewPart ∧ flip w ∈ Active} := hNew
    _ < Nat.card {v : V // v ∈ OldPart ∧ f v ∈ Active} +
          Nat.card {w : W // w ∉ NewPart ∧ flip w ∈ Active} :=
      Nat.add_lt_add_right hInside _
    _ = Nat.card {v : V // v ∈ OldPart ∧ f v ∈ Active} +
          Nat.card {v : V // v ∉ OldPart ∧ f v ∈ Active} := by rw [hOutside]
    _ = Nat.card {v : V // f v ∈ Active} := hOld.symm

/-- ONE genuine same-selected-Q original B->A source successor
has STRICTLY smaller GLOBAL B-exclusive SOURCE count, not just
a smaller local outer piece. The very same new forbidden source,
EHN map and genuine outer piece also preserve the canonical
symbol, ordered target root, full exterior source counts,
local B-active generated-boundary injectivity, A-only surviving
anchor, root seam containment and functional no-escape.

This does NOT claim that new global A-source support is unchanged. -/
theorem geometricGlobalRightFlip_actualOuterPiece_withSeamNoEscape_andStrictGlobalB
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
    (hAnchorA : f anchor ∈ fullFreeLeftExclusiveTarget iLeft jLeft)
    (hOldLocalInjection :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Old outer →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Old.functionClosure
            (gaifmanNeighborhood Old.graph
              (componentFrom Old.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) 
    (hOuterRootInSeam : Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (hFiniteNew : Finite V') (flip : V' → UT)
      (newOuter : GeometricFunctionalPieceData New n),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ i : Fin n, flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old hFinite hOld outer hn =
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
      (∀ (y : {w : V' //
          w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
        y.1 ∈ geometricPieceVertices New newOuter →
        y.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) y)))) ∧
      ∃ anew : V',
        anew ∈ geometricPieceVertices New newOuter ∧
        flip anew = f anchor ∧
        flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft ∧
        Set.range newOuter.roots ⊆
          weakFreeRootPart (sL := iLeft) (iL := jLeft) flip ∧
        FunctionalContextNoEscapeOutsideSeam New
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
          (geometricPieceVertices New newOuter) ∧
        Nat.card {w : V' //
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  obtain ⟨V', New, hNew, hFiniteNew, flip, newOuter,
      hFlip, hCoords, hSymbol, hLocalB, hExterior,
      hLocalInjection, anew, haOuter, haSame, haA,
      hNewRootSeam, hNoEscape⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withSeamAndNoEscape
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
      anchor hAnchorOuter hAnchorA hOldLocalInjection
      hOuterRootInSeam
  have hGlobalB :
      Nat.card {w : V' //
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
    finiteSource_strict_global_active_of_inside_and_exterior
      hFinite hFiniteNew
      (geometricPieceVertices Old outer)
      (geometricPieceVertices New newOuter)
      f flip (fullFreeRightExclusiveTarget iRight jRight)
      hLocalB
      (hExterior (fullFreeRightExclusiveTarget iRight jRight))
  exact ⟨V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hCoords, hSymbol, hLocalB, hExterior,
    hLocalInjection, anew, haOuter, haSame, haA,
    hNewRootSeam, hNoEscape, hGlobalB⟩

end AllThoseRamseyClasses.Lifts
