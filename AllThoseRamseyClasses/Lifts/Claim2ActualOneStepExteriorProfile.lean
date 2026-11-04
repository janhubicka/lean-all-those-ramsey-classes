import AllThoseRamseyClasses.Lifts.Claim2ActualOneStepContextualFlip
import AllThoseRamseyClasses.Lifts.OriginalGeometricPieceToNewContextProfile
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge
import AllThoseRamseyClasses.Lifts.Claim2TerminalLeftSupportAccounting

/-!
# Track C: exact exterior A-source support on the SAME actual B→A flip

The merged same-witness contextual profile theorem proved that
one genuine original-global B→A inner replacement strictly lowers
B-exclusive SOURCE support inside the transported outer context
while preserving every rooted forbidden incompatibility test.

The original flip mechanism also proves exact agreement of the
new EHN map with the old EHN map on the ENTIRE old native
functional complement. That certificate was previously discarded
by the existential contextual theorem, preventing integration
with the independently verified exterior A-source support theorem.

This module exposes the certificate on the SAME replacement
source, and composes it with the original old/new full-amalgam
exterior-cardinality equality. For one concrete New, Q, iQ, iE,
and flip it simultaneously establishes:

* an actual F-member with full native functional amalgam;
* agreement on EVERY complement vertex, not only root tuples;
* complete old/new outer-rooted all-test incompatibility profile;
* original outer-root coordinates and their exact target images;
* strictly smaller B-only SOURCE count inside the new context;
* exactly unchanged A-only SOURCE count outside that context.

The new context is still only known closed; recognition as a genuine
minimal-separator geometric piece is a separate Track A obligation.
No intermediate A-support minimality, weak-image quotient or
global target-map injectivity is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One actual right-to-left forbidden-source flip has the COMPLETE
outer-rooted all-test incompatibility profile of the original
geometric outer piece, plus strict local original B-exclusive
SOURCE support decrease on exactly the SAME replacement witness.

The induced new context may not yet be a geometric minimal-cut
piece; the proposition accurately records that distinction. -/
theorem geometricGlobalRightFlip_outerContextProfile_strictLocalExteriorSupport
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
          (geometricGlobalComplementChart Forbidden d).rootEmbedding iQ iE ∧
        ∃ (flip : V' → UT),
          New.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
            flip (iE b) = f b.1) ∧
          ∃ (hNewK : New.IsClosed
              (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)))
            (newRoot : Structure.Embedding
              (geometricGlobalFunctionalChart Forbidden P).root
              (New.induce
                (iQ '' (Set.univ : Set Q.Carrier) ∪
                  iE '' (oldOuterContextInInnerComplement Forbidden P d))
                hNewK)),
            (functionalDiagramPieceSetoid
                (geometricGlobalFunctionalChart Forbidden P).root F).r
              (geometricGlobalFunctionalChart Forbidden P).ext
              ({ Carrier := {w : V' //
                    w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                      iE '' (oldOuterContextInInnerComplement Forbidden P d))},
                 str := New.induce
                  (iQ '' (Set.univ : Set Q.Carrier) ∪
                    iE '' (oldOuterContextInInnerComplement Forbidden P d))
                  hNewK,
                 rootEmbedding := newRoot } :
                FunctionalRootExtension
                  (geometricGlobalFunctionalChart Forbidden P).root) ∧
            (∀ i : Fin n,
              (newRoot i).1 =
                iE (⟨P.roots i, hOuterRootOutside i⟩ :
                  (geometricGlobalComplementChart Forbidden d).Carrier) ∧
              flip ((newRoot i).1) = f (P.roots i)) ∧
            Nat.card {w : V' //
              w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
              flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
            Nat.card {v : V //
              v ∈ geometricPieceVertices Forbidden P ∧
              f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
            Nat.card {w : V' //
              w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
              flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
            Nat.card {v : V //
              v ∉ geometricPieceVertices Forbidden P ∧
              f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  obtain ⟨V', New, hNew, Q, hInnerProfile, iQ, iE, hNewFree,
      flip, hFlip, hSameComplement, _hClosed, _hRootInjective,
      hRootFixed, hLocalDrop⟩ :=
    geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile_andComplementAgreement
      F hFiniteF Forbidden hFinite hForbidden
      P d hm hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  have hRootInside : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Forbidden P := by
    intro i
    exact hInnerInside (Or.inl ⟨i, rfl⟩)
  have hComponentInside :
      functionalComponentFrom Forbidden
        (Set.range d.roots) d.left ⊆
      geometricPieceVertices Forbidden P := by
    intro z hz
    exact hInnerInside (Or.inr hz)
  have hDiagramProfile :
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Forbidden d).root F).r
        (geometricGlobalFunctionalChart Forbidden d).ext Q :=
    (functionalDiagramPiece_equiv_iff_glue
      (geometricGlobalFunctionalChart Forbidden d).root F
      (geometricGlobalFunctionalChart Forbidden d).ext Q).mpr
      hInnerProfile
  obtain ⟨hNewK, newRoot, hProfile, hNewRootCoordinates⟩ :=
    geometricOriginalPiece_profile_equiv_transportContext
      F Forbidden P d hRootInside hComponentInside
      hOuterRootOutside Q hDiagramProfile New iQ iE hNewFree
  letI : Finite V := hFinite
  letI : Finite V' := hFiniteF New hNew
  have hOutsideA :
      Nat.card {w : V' //
        w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : V //
        v ∉ geometricPieceVertices Forbidden P ∧
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} :=
    geometricInnerSubpiece_outsideSupport_card_eq
      Forbidden P d hInnerInside Q New iQ iE hNewFree
      f flip (fullFreeLeftExclusiveTarget iLeft jLeft)
      hSameComplement
  refine ⟨V', New, hNew, Q, iQ, iE, hNewFree,
    flip, hFlip, hSameComplement, hNewK, newRoot,
    hProfile, ?_, hLocalDrop, hOutsideA⟩
  intro i
  constructor
  · exact hNewRootCoordinates i
  · rw [hNewRootCoordinates i]
    exact (hRootFixed i).2

end AllThoseRamseyClasses.Lifts
