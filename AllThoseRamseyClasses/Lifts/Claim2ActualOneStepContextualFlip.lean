import AllThoseRamseyClasses.Lifts.Claim2ContextualFlipPackage
import AllThoseRamseyClasses.Lifts.GlobalFlipOuterRootStrictSupport

/-!
# Claim 2: one ACTUAL forbidden-source B-to-A flip and its local descent

The existential global flip in the validated functional lifting
library constructs a single genuine new forbidden source and EHN
map, a replacement root extension, and a FULL native free-amalgam
diagram over the unchanged complement.

This module uses that SAME witness for the support counting and
the contextual package, combining in one statement:
* a genuine forbidden member after the flip;
* the complete native functional free-amalgam replacement diagram;
* function-closedness of the transported old outer context;
* injective survival of the original ordered outer root and its
  exact original target coordinates; and
* a strict decrease in B-exclusive SOURCE count INSIDE that context.

The strengthened theorem also exports the *actual replacement* Q's
full canonical-gluing equivalence class; the original API is retained
as a backwards-compatible corollary.

This does not assert that the new closed context is a geometric
minimal-separator piece, nor that its complete rooted all-test
incompatibility profile equals the original. It is an actual
one-step input to, but NOT an instantiation of, the separate
finite iteration theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual native B-to-A replacement of an inner one-sided
geometric forbidden piece inside a fixed outer geometric piece
produces ONE forbidden source/New EHN map witnessing both
original-root preservation and strict LOCAL right-exclusive
source-support descent.

There is no global injectivity assumption on the weak source
map; only the inner separating root's target coordinates must be
injective. The new context is closed but is NOT declared to be
a new minimal-separator piece or to preserve its full profile. -/
theorem geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Forbidden n)
    (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (hInnerInside :
      geometricPieceVertices Forbidden d ⊆
        geometricPieceVertices Forbidden P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V'), F New ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (hInnerProfile : (functionalRootPieceSetoid
          (geometricGlobalFunctionalChart Forbidden d).root F).r
            (geometricGlobalFunctionalChart Forbidden d).ext Q)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding
          iQ iE ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          New.IsClosed
            (iQ '' (Set.univ : Set Q.Carrier) ∪
              iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
          Function.Injective
            (fun i : Fin n =>
              iE (⟨P.roots i, hOuterRootOutside i⟩ :
                (geometricGlobalComplementChart Forbidden d).Carrier)) ∧
          (∀ i : Fin n,
            iE (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Forbidden d).Carrier) ∈
              (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
            flip (iE (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Forbidden d).Carrier)) =
                f (P.roots i)) ∧
          Nat.card {w : V' //
            w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
              iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
            flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            v ∈ geometricPieceVertices Forbidden P ∧
            f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  classical
  let Compl := geometricGlobalComplementChart Forbidden d
  obtain ⟨Q, hEquivalent, g, _hg,
      V', New, hNew, iQ, iE, hNewFree,
      flip, hFlip, hQImage, hEImage⟩ :=
    geometricGlobalCommonFullLiftFlip_rightToLeft
      F Forbidden hFinite hForbidden
      d hm Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hInnerRoots hInnerNoLeft
      hInnerRootInjective
  let oldCompl : Structure.Embedding Compl.str Forbidden :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite V' := hFiniteF New hNew
  letI : Fintype V' := Fintype.ofFinite V'
  letI : Finite Compl.Carrier :=
    Finite.of_injective (fun b : Compl.Carrier => b.1)
      (by intro a b hab; exact Subtype.ext hab)
  letI : Fintype Compl.Carrier := Fintype.ofFinite Compl.Carrier
  have hOldComplement : ∀ b : Compl.Carrier,
      f (oldCompl b) = f b.1 := by
    intro b
    rfl
  have hOldOutside : ∀ b : Compl.Carrier,
      oldVertex ≠ oldCompl b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbComponent : b.1 ∈
        functionalComponentFrom Forbidden (Set.range d.roots)
          d.left := hv ▸ hvComponent
    exact b.2 hbComponent
  have hNewPieceAvoid : ∀ a : Q.Carrier,
      flip (iQ a) ∉ fullFreeRightExclusiveTarget iRight jRight := by
    intro a
    rw [hQImage a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iRight iLeft jRight jLeft hFree.swap (g a)
  have hTargetAgreeR (r : UX) :
      jRight (iRight r) = jLeft (iLeft r) := by
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hvRightSwapped :
      oldVertex ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hvRight.1, ?_⟩
    intro hr
    obtain ⟨x, hx⟩ := hr
    apply hvRight.2
    exact ⟨x, (hTargetAgreeR x).symm.trans hx⟩
  have hvRightTarget :
      f oldVertex ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive
      iRight jRight f oldVertex).mp hvRightSwapped
  have hStrictGlobal :
      Nat.card {v : V' //
        flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := oldCompl)
      (iNewL := iQ)
      (iNewR := iE)
      (sNewL := Q.rootEmbedding)
      (sRight := Compl.rootEmbedding)
      hNewFree f flip (fun b : Compl.Carrier => f b.1)
      hOldComplement hEImage
      (fullFreeRightExclusiveTarget iRight jRight)
      hNewPieceAvoid oldVertex hvRightTarget hOldOutside
  obtain ⟨hClosed, hRootInjective, hRootFixed, hLocalDrop⟩ :=
    geometricInnerSubpiece_closed_fixedRoot_strictLocalRightSupport
      Forbidden P d hInnerInside hOuterRootOutside
      Q New iQ iE hNewFree f flip
      (fullFreeRightExclusiveTarget iRight jRight)
      hEImage hStrictGlobal
  exact ⟨V', New, hNew, Q, hEquivalent, iQ, iE, hNewFree,
    flip, hFlip, hClosed, hRootInjective, hRootFixed, hLocalDrop⟩


/-- Backwards-compatible form of the genuine contextual flip.
The strengthened theorem above exposes the FULL inner canonical
profile witness used by the very same forbidden-source replacement.
All pre-existing outputs and assumptions remain unchanged. -/
theorem geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Forbidden n)
    (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (hInnerInside :
      geometricPieceVertices Forbidden d ⊆
        geometricPieceVertices Forbidden P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V'), F New ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding
          iQ iE ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          New.IsClosed
            (iQ '' (Set.univ : Set Q.Carrier) ∪
              iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
          Function.Injective
            (fun i : Fin n =>
              iE (⟨P.roots i, hOuterRootOutside i⟩ :
                (geometricGlobalComplementChart Forbidden d).Carrier)) ∧
          (∀ i : Fin n,
            iE (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Forbidden d).Carrier) ∈
              (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
            flip (iE (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Forbidden d).Carrier)) =
                f (P.roots i)) ∧
          Nat.card {w : V' //
            w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
              iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
            flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            v ∈ geometricPieceVertices Forbidden P ∧
            f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  obtain ⟨V', New, hNew, Q, _hInnerProfile, iQ, iE, hNewFree,
      flip, hFlip, hClosed, hRootInjective, hRootFixed, hLocalDrop⟩ :=
    geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile
      F hFiniteF Forbidden hFinite hForbidden
      P d hm hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  exact ⟨V', New, hNew, Q, iQ, iE, hNewFree,
    flip, hFlip, hClosed, hRootInjective, hRootFixed, hLocalDrop⟩

end AllThoseRamseyClasses.Lifts
