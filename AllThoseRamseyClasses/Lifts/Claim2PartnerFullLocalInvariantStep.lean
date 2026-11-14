import AllThoseRamseyClasses.Lifts.Claim2SameWitnessGeometricStateStep
import AllThoseRamseyClasses.Lifts.Claim2PartnerProperInnerSubpiece
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents

/-!
# Track B: matched boundary yields one full-invariant genuine selected-Q flip

Refines the already checked matched-boundary source proof: construct
the SAME actual inner piece d from the matched generated functional
boundary, then invoke the SAME-Q actual outer-state theorem with
root-coordinate and B-active generated-boundary injectivity included.

The old root-injection and old piece-local B-boundary-injection
conditions are explicit.  This does not rule out smaller-root capture
or A-mixedness in the unmatched-boundary case, nor prove the initial
original minimizer satisfies these properties.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual matched generated boundary gives ONE new source with
strict literal B-rank descent, unchanged original global symbol,
exterior SOURCE-count conservation, an A anchor, and both target-root
and local B-active boundary injectivity preserved.  This is a
partner-branch theorem only, not an unrestricted positive-rank theorem. -/
theorem claim2_actualGeometricRightFlip_of_boundaryPartner_withFullLocalInvariants
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
    (hInjT : Set.InjOn f T)
    (hOldOuterRootTargetInj :
      Function.Injective (fun i : Fin n => f (P.roots i)))
    (hOldActiveBoundaryInj :
      ∀ (z : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        z.1 ∈ geometricPieceVertices Forbidden P →
        z.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Forbidden.functionClosure
            (gaifmanNeighborhood Forbidden.graph
              (componentFrom Forbidden.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) z)))) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Forbidden m),
      0 < m ∧
      geometricPieceVertices Forbidden d ⊂
        geometricPieceVertices Forbidden P ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New)
        (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (hSelected :
          (FunctionalRootExtension.toEnumeratedRootedPattern
            (geometricGlobalFunctionalChart Forbidden d).root
            (Equiv.refl (Fin m)) Q) ∈
              forbiddenGeometricFunctionalPieces F m)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New)
        (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding
          iQ iE)
        (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ q : Q.Carrier,
          flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) ∧
        (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
          flip (iE b) = f b.1) ∧
        (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Forbidden P d)) =
            geometricPieceVertices New newOuter ∧
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
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Forbidden P ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft) ∧
        Function.Injective (fun i : Fin n => flip (newOuter.roots i)) ∧
        (∀ (z : V')
          (hzPart : z ∈ geometricPieceVertices New newOuter)
          (hzB : flip z ∈ fullFreeRightExclusiveTarget iRight jRight)
          (hzOutside : flip z ∉ Set.range (jLeft.comp iLeft)),
          Set.InjOn flip
            (New.functionClosure
              (gaifmanNeighborhood New.graph
                (componentFrom New.graph
                  (flip ⁻¹' Set.range (jLeft.comp iLeft))
                  (⟨z, hzOutside⟩ :
                    {w : V' // w ∉ flip ⁻¹' Set.range (jLeft.comp iLeft)}))))) := by
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
  have hAnchorOuter : a ∈ geometricPieceVertices Forbidden P :=
    Or.inr haOuter
  have hAnchorA : f a ∈ fullFreeLeftExclusiveTarget iLeft jLeft :=
    (weakFreeLeftPart_iff_targetExclusive iLeft jLeft f a).mp haLeft
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE,
      hNewFree, hFiniteNew, flip, newOuter,
      hFlip, hQNoRight, hEAgree, hCarrier,
      hTargetCoords, hSymbol, hRank, hExterior,
      anew, haNewOuter, haSame, haNewA, hNewRootInj, hNewBoundaryInj⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorRootAndBoundaryInj
      F hFiniteF Forbidden hFinite hForbidden
      P d hm hn hProper.subset hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRootInSeam hNoA hRootInj
      x.1 hxD hxRight a hAnchorOuter hAnchorA
      hOldOuterRootTargetInj hOldActiveBoundaryInj
  exact ⟨m, d, hm, hProper, V', New, hNew,
    Q, hSelected, iQ, iE, hNewFree,
    hFiniteNew, flip, newOuter, hFlip,
    hQNoRight, hEAgree, hCarrier,
    hTargetCoords, hSymbol, hRank, hExterior,
    anew, haNewOuter, haSame, haNewA, hNewRootInj, hNewBoundaryInj⟩

end AllThoseRamseyClasses.Lifts
