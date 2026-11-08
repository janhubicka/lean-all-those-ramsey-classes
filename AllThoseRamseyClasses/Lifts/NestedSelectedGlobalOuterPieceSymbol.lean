import AllThoseRamseyClasses.Lifts.NestedGeometricOuterReconstructionFromSelectedQ
import AllThoseRamseyClasses.Lifts.GeometricNestedActualContextCarrier
import AllThoseRamseyClasses.Lifts.SelectedReplacementCompleteComponentWitness
import AllThoseRamseyClasses.Lifts.GeometricPieceReorderSwap
import AllThoseRamseyClasses.Lifts.GeometricFlipGlobalSymbolCongruence
import AllThoseRamseyClasses.Lifts.GeometricFlipGlobalSymbolFromBoundaries
import AllThoseRamseyClasses.Lifts.SelectedGeometricFlipSourceFinite

/-!
# Restore the ACTUAL older global piece symbol after a nested canonical inner flip

The true Section 3 Claim 2 contextual source replacement must preserve
the ORIGINAL globally indexed canonical symbol for an older geometric
piece. The argument requires more than equality of incompatibility
profiles: the OLD ordered full functional root and the actual
orientation towards the newly inserted Q component must survive.

This integration imports the genuine nested source geometry,
canonical-Q complete-component witness, actual transported
context-carrier identity, native root re-enumeration and side swap,
and the proved full-root/all-test global symbol congruence.

The theorem is conditional on a genuine original nested pair, on the
genuinely geometrically selected replacement Q, and on the FULL native
forbidden source diagram New = Q +_U oldComplement, with its inherited
all-test diagram-equivalence certificate. It derives finiteness of the
new source, its true older separator, prescribed ordered root, correct
new-Q-side orientation, exact full context carrier, and equality of
the published global piece symbols.

The main result retains the exact transported geometric outer carrier.
The original global-symbol-only theorem is now its direct corollary,
so the geometric proof is not duplicated in the local-rank module.
The stronger interface and this consolidation require exact-head CI
and axiom audit. The unrestricted printed Claim 2, weak target-image
root collisions and maximal-lift strong amalgamation remain separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type}

/-- Return BOTH the global-symbol identity and the carrier equality
for the SAME genuinely selected replacement and same new source. -/
theorem nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (hm : 0 < m) :
    ∃ (hFiniteNew : Finite W)
      (newOuter : GeometricFunctionalPieceData New m),
      (∀ i : Fin m,
        newOuter.roots i =
          iE (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
              (geometricGlobalComplementChart Old inner).Carrier)) ∧
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm =
        geometricGlobalPieceSymbol F New
          hFiniteNew hFNew newOuter hm ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter := by
  let hFiniteNew : Finite W :=
    finiteSource_of_selectedGeometricFlip
      F Old inner Q hSelected New iQ iE hFree
  letI : Finite W := hFiniteNew
  let Comp := geometricGlobalComplementChart Old inner
  let oldE : Structure.Embedding Comp.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let T : Set Comp.Carrier := oldE ⁻¹' Set.range outer.roots
  have hOuterSurvive : ∀ i : Fin m,
      outer.roots i ∉
        functionalComponentFrom Old
          (Set.range inner.roots) inner.left :=
    nestedGeometric_outerRoot_avoids_innerComponent
      Old inner outer hNested
  let roots : Fin m → W :=
    fun i => iE
      (⟨outer.roots i, hOuterSurvive i⟩ : Comp.Carrier)
  have hRootImage : Set.range roots = iE '' T := by
    apply Set.Subset.antisymm
    · rintro w ⟨i, rfl⟩
      exact ⟨(⟨outer.roots i, hOuterSurvive i⟩ : Comp.Carrier),
        ⟨i, rfl⟩, rfl⟩
    · rintro w ⟨b, hbT, rfl⟩
      change oldE b ∈ Set.range outer.roots at hbT
      obtain ⟨i, hi⟩ := hbT
      refine ⟨i, ?_⟩
      exact congrArg iE (Subtype.ext hi)
  have hRootInj : Function.Injective roots :=
    (geometricTransportedOuterRoot_closed_and_injective
      Old outer inner hOuterSurvive New iE).2
  obtain ⟨dQ, hQBoundary, hAllQ⟩ :=
    selectedReplacementPiece_completeComponentWitness
      F (geometricGlobalFunctionalChart Old inner).root Q hSelected
  obtain ⟨k, dWrongSide, hOldRoot, _hExterior, hQSide⟩ :=
    nestedGeometric_outerPiece_after_fullSelectedReplacement
      Old inner outer hNested Q New iQ iE hFree
      dQ hQBoundary
  have hCorrectCut :
      Set.range roots = Set.range dWrongSide.roots :=
    hRootImage.trans hOldRoot.symm
  obtain ⟨newOuter, hReorder, hNewLeft, _hNewRight, _hRange⟩ :=
    geometricPiece_reorderRoot_and_swap
      New dWrongSide roots hRootInj hCorrectCut
  obtain ⟨xNew, hxQ, hContextCarrier⟩ :=
    nestedGeometric_actualTransportContext_eq_outerComponent
      Old inner outer hNested Q New iQ iE hFree
      dQ hQBoundary hAllQ
  have hNewRootSet : Set.range newOuter.roots = iE '' T := by
    rw [hReorder]
    exact hRootImage
  have hNewSameBase : newOuter.left.1 = xNew.1 := by
    calc
      newOuter.left.1 = dWrongSide.right.1 := hNewLeft
      _ = iQ dQ.1 := hQSide
      _ = xNew.1 := hxQ.symm
  have hNewComponent :
      componentFrom New.graph (Set.range newOuter.roots)
          newOuter.left =
      componentFrom New.graph (iE '' T) xNew :=
    sourceGaifmanComponent_eq_of_cut_eq
      New hNewRootSet newOuter.left xNew hNewSameBase
  have hExactContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
        geometricPieceVertices New newOuter := by
    calc
      (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old outer inner)) =
        (iE '' T) ∪ componentFrom New.graph (iE '' T) xNew :=
          hContextCarrier
      _ = geometricPieceVertices New newOuter := by
        change (iE '' T) ∪
          componentFrom New.graph (iE '' T) xNew =
          Set.range newOuter.roots ∪
          componentFrom New.graph
            (Set.range newOuter.roots) newOuter.left
        rw [hNewComponent, hNewRootSet]
  have hInnerRoot : ∀ i : Fin n,
      inner.roots i ∈ geometricPieceVertices Old outer :=
    nestedGeometric_innerRoot_in_outerPiece
      Old inner outer hNested
  have hInnerComponent :
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left ⊆
        geometricPieceVertices Old outer := by
    intro v hv
    exact Or.inr (hNested hv)
  have hRootCoordinates : ∀ i : Fin m,
      newOuter.roots i =
        iE (⟨outer.roots i, hOuterSurvive i⟩ : Comp.Carrier) := by
    intro i
    exact congrFun hReorder i
  have hSymbol :
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm =
        geometricGlobalPieceSymbol F New
          (inferInstance : Finite W) hFNew newOuter hm :=
    geometricFlip_preserves_globalPieceSymbol_of_newGeometricContext
      F Old hFOld outer inner
      hInnerRoot hInnerComponent hOuterSurvive
      Q hEq New hFNew iQ iE hFree
      newOuter hRootCoordinates hExactContext hm
  exact ⟨hFiniteNew, newOuter, hRootCoordinates, hSymbol, hExactContext⟩

/-- A genuinely selected nested FULL native canonical replacement
preserves the actual old outer global canonical piece symbol, using
the exact original ordered outer root and selecting the new inserted
Q-side component rather than the retained older exterior.

The selected Q source certificate is indispensable: equivalent
rooted incompatibility profiles alone do not imply whole-private-side
connectivity. The map to an external weak EHN target is not used. -/
theorem nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (hm : 0 < m) :
    ∃ (hFiniteNew : Finite W)
      (newOuter : GeometricFunctionalPieceData New m),
      (∀ i : Fin m,
        newOuter.roots i =
          iE (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
              (geometricGlobalComplementChart Old inner).Carrier)) ∧
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm =
        geometricGlobalPieceSymbol F New
          hFiniteNew hFNew newOuter hm := by
  obtain ⟨hFiniteNew, newOuter, hRoots, hSymbol, _hCarrier⟩ :=
    nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier
      F Old hFOld inner outer hNested
      Q hSelected hEq New hFNew iQ iE hFree hm
  exact ⟨hFiniteNew, newOuter, hRoots, hSymbol⟩

end AllThoseRamseyClasses.Lifts
