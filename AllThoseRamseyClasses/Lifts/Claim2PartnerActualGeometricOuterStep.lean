import AllThoseRamseyClasses.Lifts.Claim2PartnerProperInnerSubpiece
import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents

/-!
# Actual outer geometric successor from a genuine matched boundary partner

A matched complete native functional boundary partner and an
injective image of its entire root produce a proper B-only source
inner piece via the existing verified source theorem. Its SAME
replacement Q is genuinely selected and its canonical flip now
constructs an actual outer geometric minimal-separator piece
with the original ordered root, full global canonical symbol
and a STRICTLY smaller B-exclusive SOURCE-vertex count.

Unlike the earlier 2019 proof, the new outer source is not merely
a closed contextual rooted profile. This reuses the verified
same-Q concrete selected geometric replacement #929 rather
than choosing any independent replacement Q.

The statement retains the genuine opposite partner and root
injectivity hypotheses. Their singleton-boundary discharge is
a separate corollary. Positive outer root width is explicit
because its original GLOBAL canonical symbol is undefined at
zero width. No target weak-image quotient is used.

The paper's numbered source is frozen; this draft needs full
exact-head Lean CI/axioms/no-admissions verification.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A real matched boundary partner produces a real SAME-Q
B-to-A forbidden source flip with a genuine old-symbol outer
geometric piece and strictly smaller local B-source rank. -/
theorem claim2_actualGeometricRightFlip_of_boundaryPartner
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n : ℕ} (P : GeometricFunctionalPieceData Forbidden n)
    (hn : 0 < n)
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
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin n, flip (newOuter.roots i) = f (P.roots i)) ∧
        geometricGlobalPieceSymbol F Forbidden
            hFinite hForbidden P hn =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter hn ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
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
  obtain ⟨V', New, hNew, _Q, _hSelected,
      _iQ, _iE, _hNewFree, flip, hFlip, hFiniteNew,
      newOuter, _hEAgree, _hRootCoords, hTargetCoords,
      hSymbol, hRank⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport
      F hFiniteF Forbidden hFinite hForbidden
      P d hm hn hProper.subset hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRootInSeam hNoA hRootInj
      x.1 hxD hxRight
  exact ⟨m, d, hm, hProper, V', New, hNew,
    hFiniteNew, flip, newOuter, hFlip,
    hTargetCoords, hSymbol, hRank⟩

end AllThoseRamseyClasses.Lifts
