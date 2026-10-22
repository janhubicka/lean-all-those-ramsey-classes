import AllThoseRamseyClasses.Lifts.ProperRightPieceFromBoundaryPartner
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Strict right-side descent from a genuine proper boundary-partner sub-piece

This theorem connects the verified source-side construction of a
literal proper B-only sub-piece to the verified original-global
right-to-left support decrease. It does NOT posit an arbitrary
new piece or replace the weak source map by an injective map.

The new hypotheses are explicit: the generated boundary is
nonempty, its target images are pairwise distinct, and the
original full shared canonical lift exists. The existence of
a boundary partner (and injectivity of the boundary images)
is not proved by the published unrestricted Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A proper right-only component with an exact generated-boundary
partner permits an ACTUAL forbidden-source replacement reducing
the ORIGINAL right-exclusive SOURCE cardinality.

In addition to the strict decrease, we return the genuine
proper sub-piece used in the construction. There is no global
injectivity assumption on the original EHN source map. -/
theorem boundaryPartner_properRightPiece_strictRightSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
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
    {n : ℕ} (P : GeometricFunctionalPieceData Forbidden n)
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (x : {z : V // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxOld : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (T : Set V)
    (hT : T = Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside Forbidden.graph T
      (outsideCutMap hTS x) y)
    (hYBoundary : Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph T y)) = T)
    (a : V)
    (haOld : a ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (haLeft : a ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hTnonempty : T.Nonempty)
    (hInjT : Set.InjOn f T) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData Forbidden m),
      Set.range Q.roots = T ∧
      geometricPieceVertices Forbidden Q ⊂
        geometricPieceVertices Forbidden P ∧
      ∃ (V' : Type) (New : Structure L V'),
        F New ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          Nat.card {v : V' //
            flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  letI : Finite V := hFinite
  obtain ⟨m, Q, hQroot, hQcomponent, hProper, pRight, _hpRight, hMap⟩ :=
    weakRightComponent_partner_has_properRightFactor
      hFree f hf P hRoots x hxOld hxRight
      T hT hTS y hSep hYBoundary a haOld haLeft
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    obtain ⟨t, ht⟩ := hTnonempty
    have htRange : t ∈ Set.range Q.roots := by
      rw [hQroot]
      exact ht
    obtain ⟨i, _⟩ := htRange
    subst m
    exact Fin.elim0 i
  have hRootsQ : Set.range Q.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f := by
    rw [hQroot]
    exact hTS
  have hRootImageInjective :
      Function.Injective (fun i : Fin m => f (Q.roots i)) := by
    intro i j hij
    apply Q.roots_injective
    apply hInjT
    · rw [← hQroot]
      exact ⟨i, rfl⟩
    · rw [← hQroot]
      exact ⟨j, rfl⟩
    · exact hij
  have hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range Q.roots) Q.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f := by
    intro z hzC hzLeft
    let zP : geometricPieceVertices Forbidden Q :=
      ⟨z, Or.inr hzC⟩
    have hRightImage : f z = jRight (pRight zP) :=
      (hMap zP).symm
    exact (weakFreeLeftPart_not_right
      hFree f hzLeft (pRight zP)) hRightImage
  have hxQ : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range Q.roots) Q.left := by
    rw [hQcomponent]
    exact componentFrom_root Forbidden.graph
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x
  obtain ⟨V', New, hNew, flip, hFlip, hDecrease⟩ :=
    geometricGlobalCommonFullLiftFlip_strict_rightSupport
      F hFiniteF Forbidden hFinite hForbidden
      Q hm Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon hRootsQ hNoLeft
      hRootImageInjective x.1 hxQ hxRight
  exact ⟨m, Q, hQroot, hProper, V', New,
    hNew, flip, hFlip, hDecrease⟩

end AllThoseRamseyClasses.Lifts
