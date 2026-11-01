import AllThoseRamseyClasses.Lifts.Claim2ActualOneStepContextualFlip
import AllThoseRamseyClasses.Lifts.OriginalGeometricPieceToNewContextProfile
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge

/-!
# Track C: all-test outer profile and strict local B-source descent in one actual flip

For ONE concrete genuine B-to-A forbidden-source replacement, we
combine two already separately validated mechanisms:

* the actual source and target-map flip with a strictly decreasing
  B-exclusive SOURCE count inside the function-closed transported
  context, including exact preservation of the old root coordinates;
* Track B's complete all-test incompatibility congruence between the
  original genuine outer geometric piece and the new transported
  CONTEXT, in its own FULL native functional induced structure.

The inner replacement Q is the SAME witnessed rooted extension in
both the strict-count proof and the full-profile transfer. Its
canonical-gluing equivalence class is exposed by the strengthened
actual one-step flip and converted to actual-diagram equivalence via
the already proved canonical glue/diagram bridge.

This is an important concrete piece of the printed Claim 2 iteration.
It does not reclassify the new context as a genuine geometric piece:
the minimal closed separating root and selected component must still
be recovered (Track A). Moreover it does not establish existence of
another next flip or the terminal A-to-B contradiction. Both remain
separate explicit obligations; no manuscript prose is changed.
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
theorem geometricGlobalRightFlip_outerContextProfile_strictLocalRightSupport
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
              ({ Carrier :=
                  (iQ '' (Set.univ : Set Q.Carrier) ∪
                    iE '' (oldOuterContextInInnerComplement Forbidden P d)),
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
              flip (newRoot i).1 = f (P.roots i)) ∧
            Nat.card {w : V' //
              w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
              flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
            Nat.card {v : V //
              v ∈ geometricPieceVertices Forbidden P ∧
              f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  classical
  obtain ⟨V', New, hNew, Q, hInnerProfile, iQ, iE, hNewFree,
      flip, hFlip, _hClosed, _hRootInjective, hRootFixed, hLocalDrop⟩ :=
    geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile
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
  refine ⟨V', New, hNew, Q, iQ, iE, hNewFree,
    flip, hFlip, hNewK, newRoot, hProfile, ?_, hLocalDrop⟩
  intro i
  constructor
  · exact hNewRootCoordinates i
  · rw [hNewRootCoordinates i]
    exact (hRootFixed i).2

end AllThoseRamseyClasses.Lifts
