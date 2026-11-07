import AllThoseRamseyClasses.Lifts.NestedSelectedGlobalOuterPieceSymbol

/-!
# Track A/C: genuine older geometric source piece with local B-support decrease

This proof refines the already verified actual nested global-symbol
construction by retaining its internal EXACT entire source CARRIER
identity, rather than forgetting that identity in the existential
conclusion. Thus the same Q and the same New map support both the
original global symbol and a strict local B-only SOURCE vertex rank drop.

The existing proof of global symbol preservation is repeated here
temporarily to expose its private carrier lemma without altering the
verified public theorem. Once CI validates the strengthened interface,
the original theorem can be refactored into a corollary, avoiding
permanent proof duplication.

No root collision is resolved; the successor and terminal A-minimality
contradiction in the printed Claim 2 remain separate obligations.
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


/-- A strict B-exclusive SOURCE-vertex count decrease on the same
transported closed context is a strict decrease on the vertex
set of an ACTUAL geometric minimal-closed-separator piece,
with its entire original ordered root and global symbol.

The theorem retains its exact carrier equation, to avoid
identifying two separately chosen existential replacements. -/
theorem nestedGeometric_selectedFlip_strictLocalRank_on_newGeometricPiece
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
    (hm : 0 < m)
    {UT : Type}
    (f : V → UT) (flip : W → UT)
    (BOnly : Set UT)
    (hStrictContext :
      Nat.card {w : W //
        w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old outer inner)) ∧
        flip w ∈ BOnly} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ BOnly}) :
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
          geometricPieceVertices New newOuter ∧
      Nat.card {w : W //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ BOnly} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Old outer ∧
          f v ∈ BOnly} := by
  obtain ⟨hFiniteNew, newOuter, hRoots, hSymbol, hCarrier⟩ :=
    nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier
      F Old hFOld inner outer hNested
      Q hSelected hEq New hFNew iQ iE hFree hm
  have hRank :
      Nat.card {w : W //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ BOnly} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Old outer ∧
          f v ∈ BOnly} := by
    rw [← hCarrier]
    exact hStrictContext
  exact ⟨hFiniteNew, newOuter, hRoots, hSymbol, hCarrier, hRank⟩

end AllThoseRamseyClasses.Lifts
