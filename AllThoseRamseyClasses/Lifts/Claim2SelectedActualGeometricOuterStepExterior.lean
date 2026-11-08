import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.NestedSelectedGeometricFullSourceInvariants

/-!
# Actual one-step Claim 2 flip: all outer geometric state invariants

For one same-witness genuine right-to-left B-only source-piece flip
across a common full global canonical lift, construct one actual
new forbidden source and new geometric outer piece having the same:
* original ordered full outer root and its weak target coordinates;
* original globally indexed 2019 piece symbol and all forbidden tests;
* retained complete complement with literally unchanged weak target map.

The B-exclusive SOURCE count inside the actual geometric outer piece
strictly decreases, and for EVERY target subset (in particular both
A- and B-exclusive parts) the number of SOURCE vertices outside
the entire old/new outer pieces is EXACTLY equal.

This strengthening applies the generic source-invariant package to
the SAME Q returned by the already verified original strict local
flip, not to a separately selected existential Q.

It remains conditional on finding a suitable B-only inner geometric
piece with an injective INNER target root image. Neither existence
of such a piece at every positive-rank state nor the terminal
A-exclusive source minimizer contradiction is asserted.
No collision assumption on the OUTER target root is introduced.

This new module will replace a duplicated proof only AFTER Lean
CI validates the stronger interface; numbered 2019 text is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The concrete same-selected-Q B-to-A flip with an ACTUAL
minimal-separator outer successor and exact exterior support
invariance for ALL target subsets, in addition to the strict
interior B-exclusive SOURCE count decrease. -/
theorem geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior
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
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (hSelected :
        (FunctionalRootExtension.toEnumeratedRootedPattern
          (geometricGlobalFunctionalChart Old inner).root
          (Equiv.refl (Fin m)) Q) ∈
            forbiddenGeometricFunctionalPieces F m)
      (iQ : Structure.Embedding Q.str New)
      (iE : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iE)
      (flip : V' → UT)
      (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
      (hFiniteNew : Finite V')
      (newOuter : GeometricFunctionalPieceData New n),
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (∀ i : Fin n,
        newOuter.roots i =
          iE (⟨outer.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) ∧
      (∀ i : Fin n,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
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
          f v ∈ TargetSet}) := by
  letI : Finite V := hFinite
  have hNested :
      componentFrom Old.graph
        (Set.range inner.roots) inner.left ⊆
      componentFrom Old.graph
        (Set.range outer.roots) outer.left := by
    intro v hv
    have hvOuter : v ∈ geometricPieceVertices Old outer :=
      hInnerInside (Or.inr hv)
    rcases hvOuter with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      have hNo : v ∉ componentFrom Old.graph
          (Set.range inner.roots) inner.left := by
        simpa only [hi] using hOuterRootOutside i
      exact False.elim (hNo hv)
    · exact hComponent
  obtain ⟨V', New, hNew, Q, hInnerProfile, hSelected,
    iQ, iE, hNewFree, flip, hFlip, hEAgree,
    _hClosed, _hRootInjective, _hRootFixed, hStrictContext⟩ :=
    geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile_andComplementAgreement_selected
      F hFiniteF Old hFinite hOld
      outer inner hm hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  have hDiagram :
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q :=
    (functionalDiagramPiece_equiv_iff_glue
      (geometricGlobalFunctionalChart Old inner).root
      F (geometricGlobalFunctionalChart Old inner).ext Q).mpr
      hInnerProfile
  obtain ⟨hFiniteNew, newOuter, hRootCoords,
      hSymbol, _hCarrier, hTargetCoords, hRank, hExterior⟩ :=
    nestedGeometric_selectedFlip_fullSourceStepInvariants
      F Old hOld inner outer hNested Q hSelected hDiagram
      New hNew iQ iE hNewFree hn
      f flip hEAgree (fullFreeRightExclusiveTarget iRight jRight)
      hStrictContext
  have hRootCoordsOriginal : ∀ i : Fin n,
      newOuter.roots i =
        iE (⟨outer.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old inner).Carrier) := by
    intro i
    exact hRootCoords i
  exact ⟨V', New, hNew, Q, hSelected,
    iQ, iE, hNewFree, flip, hFlip,
    hFiniteNew, newOuter, hEAgree,
    hRootCoordsOriginal, hTargetCoords, hSymbol, hRank, hExterior⟩


end AllThoseRamseyClasses.Lifts
