import AllThoseRamseyClasses.Lifts.NestedGeometricExteriorInternalBoundary
import AllThoseRamseyClasses.Lifts.GeometricOuterBoundaryFromSelectedQ
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamOuterOldRootCriterion

/-!
# Reconstruct an actual older geometric separator in the literal nested Q flip

Suppose an actual geometric inner component D of the old finite
forbidden functional source is contained in one original older
minimal-closed-separator component C. Let the selected replacement Q
have a genuine private component generating its complete functional
root U, and let New = Q +_U Complement be a literal FULL native
functional amalgam over the same unchanged complement.

We now derive BOTH complete older boundaries and an actual older
geometric minimal-separator piece in New, without assuming an older
exterior component is private or has full generated boundary.
The original nested old exterior supplies those statements by the
independent reflection theorem in NestedGeometricExteriorInternalBoundary.
The new inner opposite boundary follows from the already verified
GeometricOuterBoundaryFromSelectedQ.

This theorem concerns genuine SOURCE vertices and full native
function-value fibres, not a quotient through a weak EHN target map.
It does not assert the new piece agrees with the transported closed
context in *carrier* or all-test rooted profile, and it does not
establish Claim 2's strictly decreasing local B support.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type}

/-- Symmetry of paths with Gaifman adjacency, retaining the exact
deleted cut. The proof is independent of graph-only approximations:
the graph is the full native functional relationalization. -/
private theorem nestedSource_reachOutside_symm
    (A : Structure L V) (T : Set V)
    {x y : {z : V // z ∉ T}}
    (h : ReachOutside A.graph T x y) :
    ReachOutside A.graph T y x :=
  reachOutside_symm A.graph T h

/-- Moving the chosen basepoint within a single old T-component
does not change that component. This is what allows us to anchor
the older outer component at the selected INNER vertex. -/
private theorem nestedSource_component_eq_of_mem
    (A : Structure L V) (T : Set V)
    (x y : {z : V // z ∉ T})
    (hy : y.1 ∈ componentFrom A.graph T x) :
    componentFrom A.graph T x =
      componentFrom A.graph T y := by
  have hxy : ReachOutside A.graph T x y := hy.2
  have hyx : ReachOutside A.graph T y x :=
    nestedSource_reachOutside_symm A T hxy
  apply Set.Subset.antisymm
  · intro z hz
    exact ⟨hz.1, hyx.trans hz.2⟩
  · intro z hz
    exact ⟨hz.1, hxy.trans hz.2⟩

/-- The older outer minimal separator actually survives a full inner
replacement Q as a genuine new source-attached geometric piece.

The *single* old-side nesting hypothesis implies:
1. all older root coordinates remain in the unchanged complement;
2. the original chosen inner vertex belongs to the older C component;
3. the old C boundary is the entire older closed cut;
4. the opposite older exterior is private to U and generates the
   entire older cut *inside the unchanged complement*.

The only new-side geometric premise is a private selected Q component
with its complete generated internal root. This premise is discharged
for the exact canonical selected Q by the separate proved #805 lemma.
No additional arbitrary outer-boundary or retained-path assumption. -/
theorem nestedGeometric_outerPiece_after_fullSelectedReplacement
    [Finite W]
    (Old : Structure L V)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iCompNew : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iCompNew)
    (dQ : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding})
    (hQBoundary :
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) dQ)) =
        Set.range Q.rootEmbedding) :
    let Comp := geometricGlobalComplementChart Old inner
    let iCompOld : Structure.Embedding Comp.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range inner.roots) inner.minimal.1 inner.left
    let T : Set Comp.Carrier := iCompOld ⁻¹' Set.range outer.roots
    ∃ (k : ℕ) (newOuter : GeometricFunctionalPieceData New k),
      Set.range newOuter.roots = iCompNew '' T ∧
      (∃ xExterior : Comp.Carrier, newOuter.left.1 = iCompNew xExterior) ∧
      newOuter.right.1 = iQ dQ.1 := by
  let Comp := geometricGlobalComplementChart Old inner
  let iCompOld : Structure.Embedding Comp.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let T : Set Comp.Carrier := iCompOld ⁻¹' Set.range outer.roots
  obtain ⟨hTclosed, xExterior, hExteriorPrivate, hExteriorBoundary⟩ :=
    nestedGeometric_originalExterior_internalBoundary_eq_outerRoot
      Old inner outer hNested
  have hOuterRootOutside : ∀ i : Fin m,
      outer.roots i ∉
        functionalComponentFrom Old (Set.range inner.roots) inner.left :=
    nestedGeometric_outerRoot_avoids_innerComponent
      Old inner outer hNested
  have hTRange : iCompOld '' T = Set.range outer.roots := by
    apply Set.Subset.antisymm
    · rintro w ⟨b, hb, rfl⟩
      exact hb
    · rintro w ⟨i, rfl⟩
      exact ⟨⟨outer.roots i, hOuterRootOutside i⟩,
        ⟨i, rfl⟩, rfl⟩
  have hInnerInOuter :
      inner.left.1 ∈
        componentFrom Old.graph (Set.range outer.roots) outer.left :=
    hNested (componentFrom_root
      Old.graph (Set.range inner.roots) inner.left)
  let xOld : {v : V // v ∉ iCompOld '' T} :=
    ⟨inner.left.1, by
      rw [hTRange]
      exact hInnerInOuter.1⟩
  let xOuterCut : {v : V // v ∉ Set.range outer.roots} :=
    ⟨inner.left.1, hInnerInOuter.1⟩
  have hSameOldComponent :
      componentFrom Old.graph (iCompOld '' T) xOld =
        componentFrom Old.graph (Set.range outer.roots) outer.left := by
    calc
      componentFrom Old.graph (iCompOld '' T) xOld =
        componentFrom Old.graph (Set.range outer.roots) xOuterCut :=
          sourceGaifmanComponent_eq_of_cut_eq
            Old hTRange xOld xOuterCut rfl
      _ = componentFrom Old.graph (Set.range outer.roots) outer.left :=
        (nestedSource_component_eq_of_mem
          Old (Set.range outer.roots) outer.left
          xOuterCut hInnerInOuter).symm
  have hInnerInOldOuter :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (iCompOld '' T) xOld := by
    rw [hSameOldComponent]
    exact hNested
  have hOldOuterBoundary :
      Old.functionClosure
        (gaifmanNeighborhood Old.graph
          (componentFrom Old.graph (iCompOld '' T) xOld)) =
        iCompOld '' T := by
    rw [hSameOldComponent, hTRange]
    exact geometricPiece_left_boundary_closure Old outer
  obtain ⟨xNew, hxNew, hNewBoundary⟩ :=
    geometricGlobalSource_outerBoundary_from_selectedReplacement
      Old inner Q New iQ iCompNew hNewFree
      T hTclosed xOld
      (componentFrom_root Old.graph (Set.range inner.roots) inner.left)
      hInnerInOldOuter hOldOuterBoundary dQ hQBoundary
  have hNewPrivate : xNew.1 ∉ Set.range iCompNew := by
    rintro ⟨b, hbImage⟩
    have hOver : iQ dQ.1 = iCompNew b :=
      hxNew.symm.trans hbImage.symm
    obtain ⟨r, hrInner, _hrComp⟩ :=
      (hNewFree.overlap dQ.1 b).mp hOver
    exact dQ.2 ⟨r, hrInner.symm⟩
  have hOpposite :
      xNew.1 ∉
        iCompNew '' componentFrom Comp.str.graph T xExterior := by
    rintro ⟨b, _, hbImage⟩
    exact hNewPrivate ⟨b, hbImage⟩
  obtain ⟨k, newOuter, hRoot, hLeft, hRight, _hBoundary⟩ :=
    finite_outerOldRoot_hasGeometricPiece_of_oppositeBoundary
      hNewFree T hTclosed xExterior
      hExteriorPrivate hExteriorBoundary
      xNew hOpposite hNewBoundary
  exact ⟨k, newOuter, hRoot, ⟨xExterior.1, hLeft⟩,
    hRight.trans hxNew⟩

end AllThoseRamseyClasses.Lifts
