import AllThoseRamseyClasses.Lifts.Claim2PartnerProperInnerSubpiece
import AllThoseRamseyClasses.Lifts.Claim2ActualOneStepFullOuterProfile
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents

/-!
# Claim 2: a certified contextual B→A flip from an actual boundary partner

This module composes the genuine geometric proper-one-sided source
piece constructed from a matched generated boundary partner
with the independently kernel-verified original global canonical
source flip and the full all-test outer-context congruence.

The source is an ARBITRARY intermediate finite forbidden witness
with weak EHN map. No support-minimality of this witness (on
either target side) or minimality of the outer mixed piece is
assumed. One selected right-exclusive S-component lies inside
an actual outer geometric piece P whose ordered root is in S.
One left-exclusive vertex remains in the same outer component.

The explicit substantive hypotheses are:
* its generated closed root T has a boundary partner, so it
  produces a proper one-sided genuine geometric subpiece;
* the original map is injective on the SELECTED generated root T, so
  this subpiece has an injective target-root tuple.

The SAME actual native replacement then strictly reduces local
B-exclusive SOURCE count inside its transported outer CONTEXT
and preserves the complete forbidden incompatibility profile
of the original outer geometric piece against ALL rooted tests.
It does not yet prove the transported context is a new
minimal-separator geometric piece. That Track A reconstruction,
and the partner/injectivity conditions themselves, remain the
essential positive-B-rank successor obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An intermediate forbidden source with an actual boundary partner
and root-injectivity on its CURRENT shared seam has a *genuine
proper B-only inner source piece*, and a same-witness B-to-A
canonical flip with full outer rooted all-test equivalence,
unchanged ordered target root coordinates and strict LOCAL
right-exclusive SOURCE-support reduction.

The source need NOT minimize left support. The boundary partner
and selected-root InjOn are stated explicitly; neither is derived
merely from positive B-count. -/
theorem claim2_actualContextualRightFlip_of_boundaryPartner
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n : ℕ} (P : GeometricFunctionalPieceData Forbidden n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (x : {v : V // v ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hxOuter : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (haOuter : a ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (T : Set V)
    (hT : T = Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTS : T ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hTnonempty : T.Nonempty)
    (y : {v : V // v ∉ T})
    (hSep : ¬ ReachOutside Forbidden.graph T
      (outsideCutMap hTS x) y)
    (hYBoundary :
      Forbidden.functionClosure
        (gaifmanNeighborhood Forbidden.graph
          (componentFrom Forbidden.graph T y)) = T)
    (hInjT : Set.InjOn f T) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Forbidden m),
      0 < m ∧
      geometricPieceVertices Forbidden d ⊂
        geometricPieceVertices Forbidden P ∧
      ∃ (hOuterRootOutside : ∀ i : Fin n,
        P.roots i ∉ functionalComponentFrom Forbidden
          (Set.range d.roots) d.left),
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
              f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  classical
  letI : Finite V := hFinite
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  let AOnly : Set V :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) f
  have hSclosed : Forbidden.IsClosed S :=
    weakFreeRootPart_isClosed (sL := iLeft) (iL := jLeft) f hf.1
  have hBNoA :
      ∀ z : V, z ∈ componentFrom Forbidden.graph S x →
        z ∉ AOnly := by
    intro z hz hzA
    have hzB : z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
      weakFreePartition_component_right
        hFree f hf.1 x hxRight hz
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f)) hzA hzB
  obtain ⟨m, d, hm, hDRoot, hDRootInside, hProper,
      hDComp, hNoA, hRootInj⟩ :=
    geometricPiece_properInnerOneSided_of_boundaryPartner
      Forbidden P S hSclosed hOuterRootInSeam
      x hxOuter AOnly hBNoA a haOuter haLeft.2 haLeft
      T hT hTS hTnonempty y hSep hYBoundary
      f hInjT
  have hInnerRootInSeam :
      Set.range d.roots ⊆ S := by
    intro z hz
    exact (hDRootInside hz).1
  have hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left := by
    intro i hi
    have hiB : P.roots i ∈ componentFrom Forbidden.graph S x := by
      simpa only [hDComp] using hi
    exact hiB.1 (hOuterRootInSeam ⟨i, rfl⟩)
  have hxD : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range d.roots) d.left := by
    change x.1 ∈ componentFrom Forbidden.graph
      (Set.range d.roots) d.left
    rw [hDComp]
    exact componentFrom_root Forbidden.graph S x
  refine ⟨m, d, hm, hProper, hOuterRootOutside, ?_⟩
  exact geometricGlobalRightFlip_outerContextProfile_strictLocalRightSupport
    F hFiniteF Forbidden hFinite hForbidden
    P d hm hProper.subset hOuterRootOutside
    Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    hInnerRootInSeam hNoA hRootInj
    x.1 hxD hxRight

end AllThoseRamseyClasses.Lifts
