import AllThoseRamseyClasses.Lifts.Claim2ActualOneStepContextualFlip
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftSelectedGeometricFlip

/-!
# Genuine selected-Q certificate and strict local B support in ONE actual flip

This is an intentionally nonbreaking extension of the verified original
Track C contextual one-step theorem. The new endpoint returns all
original certificates and ALSO the geometric selected membership
of the very SAME Q used to obtain strict local right-exclusive
SOURCE-support decrease in the literal replacement New.

A separate invocation of a selected-source flip would select a
potentially different Q and cannot be combined with the old support
decrease. Instead, this proof makes the original counting and
closed-context proof consume the strengthened genuine selected
right-to-left common-lift flip (#921) without changing its
actual replacement witness, full source embeddings, or weak target map.

It does not yet assert that the resulting closed context is an
actual geometric minimal separator; that next proof can invoke the
genuine nested source geometry of Track A (#876/#892/#899)
using precisely this selected Q.

No new weak image quotient, extra root injectivity, source-map
surjectivity, or preservation of all target function fibres is assumed.
The printed 2019 text remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- ONE selected genuine canonical right-to-left source flip
simultaneously preserves the whole retained complement and old
ordered outer root, constructs a closed transported outer
context, and STRICTLY drops its local right-exclusive B-SOURCE
support. The output selected-geometric Q certificate is for
the SAME witness as the strict decrease. -/
theorem geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile_andComplementAgreement_selected
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
        (hSelected :
          (FunctionalRootExtension.toEnumeratedRootedPattern
            (geometricGlobalFunctionalChart Forbidden d).root
            (Equiv.refl (Fin m)) Q) ∈
              forbiddenGeometricFunctionalPieces F m)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding
          iQ iE ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
            flip (iE b) = f b.1) ∧
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
  obtain ⟨Q, hEquivalent, hSelected, g, _hg,
      V', New, hNew, iQ, iE, hNewFree,
      flip, hFlip, hQImage, hEImage⟩ :=
    geometricGlobalCommonFullLiftFlip_rightToLeft_selected
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
  exact ⟨V', New, hNew, Q, hEquivalent, hSelected, iQ, iE, hNewFree,
    flip, hFlip, hEImage, hClosed, hRootInjective, hRootFixed, hLocalDrop⟩


end AllThoseRamseyClasses.Lifts
