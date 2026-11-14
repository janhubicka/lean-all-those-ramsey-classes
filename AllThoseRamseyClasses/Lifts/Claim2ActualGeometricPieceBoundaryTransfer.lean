import AllThoseRamseyClasses.Lifts.Claim2PieceScopedActiveBoundaryTransfer
import AllThoseRamseyClasses.Lifts.Claim2OuterLocalBoundaryRestriction
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram
import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext

/-!
# B-active generated-boundary injection on a genuine selected-Q outer flip

Specialize the verified paired source-boundary transport and the
piece-scoped transfer to a TRUE older geometric source piece P and
an actual nested inner piece d. The old source is literally its
FULL native functional free amalgam over the complete inner root.
Its full retained E embedding is the original complement embedding.

The generated new outer geometric carrier is the union of ALL
inserted Q source vertices and the retained old context in E.
That retained context is, by its definition, the exact preimage
of the OLD geometric outer carrier under the old E embedding.

If the selected Q introduces no B-exclusive source images and the
old chosen outer piece had injected generated B-active boundaries,
the NEW chosen outer piece has injected generated B-active
boundaries. The new whole seam may still have image collisions.

There is no global seam-injectivity hypothesis, target-image
quotient, source-arity decrease or automatic positive successor.
The geometric data are exact native source structures, not
abstract isomorphism classes. The original 2019 TeX remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In one actual SAME-complement nested geometric Q replacement,
the source-side invariant required by the checked positive-rank
two-way theorem is preserved ON THE NEW geometric outer piece.

The hypotheses hNewFree, hCarrier, hSameE, and hNoNewB are exactly
the full selected-Q geometric/source certificates (not derived
from an arbitrary weak target homomorphism); the original source
free-amalgam and retained old-carrier inclusion are discharged
here by the actual old geometric piece definitions.

This theorem needs only old active-boundary injection within P,
not globally within the old forbidden source. -/
theorem geometricSelectedQ_actualOuter_preserves_BActive_boundary_inj
    {V W UX UA UB UT : Type}
    (Old : Structure L V)
    (New : Structure L W)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (newOuter : GeometricFunctionalPieceData New n)
    (Target : Structure L UT)
    (f : V → UT) (flip : W → UT)
    (X : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hInnerRootInSeam :
      Set.range inner.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hSameE : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (hCarrier :
      iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner) =
          geometricPieceVertices New newOuter)
    (hNoNewB : ∀ q : Q.Carrier,
      flip (iQ q) ∉
        fullFreeRightExclusiveTarget iRight jRight)
    (hOldActiveBoundaryInj :
      ∀ (x : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Old outer →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Old.functionClosure
            (gaifmanNeighborhood Old.graph
              (componentFrom Old.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
    ∀ (y : W)
      (hyPart : y ∈ geometricPieceVertices New newOuter)
      (hyB : flip y ∈ fullFreeRightExclusiveTarget iRight jRight)
      (hyOutside : flip y ∉ Set.range (jLeft.comp iLeft)),
      Set.InjOn flip
        (New.functionClosure
          (gaifmanNeighborhood New.graph
            (componentFrom New.graph
              (flip ⁻¹' Set.range (jLeft.comp iLeft))
              (⟨y, hyOutside⟩ :
                {w : W // w ∉ flip ⁻¹' Set.range (jLeft.comp iLeft)})))) := by
  let iOldE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  have hOldFree :=
    geometricGlobalSource_freeDiagram Old inner
  have hOldRootSeam :
      ∀ i : Fin m,
        f (iOldE
          ((geometricGlobalComplementChart Old inner).rootEmbedding i)) ∈
            Set.range (jLeft.comp iLeft) := by
    intro i
    have hRootCoord :
        iOldE
          ((geometricGlobalComplementChart Old inner).rootEmbedding i) =
            inner.roots i := rfl
    rw [hRootCoord]
    exact hInnerRootInSeam ⟨i, rfl⟩
  have hCarrierSubset :
      geometricPieceVertices New newOuter ⊆
        Set.range iQ ∪
          iE '' (iOldE ⁻¹' geometricPieceVertices Old outer) := by
    intro y hy
    have hyCarrier : y ∈
        iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old outer inner) :=
      hCarrier.symm ▸ hy
    rcases hyCarrier with hQ | hE
    · obtain ⟨q, _hq, hq⟩ := hQ
      exact Or.inl ⟨q, hq⟩
    · exact Or.inr hE
  have hOldScoped :=
    claim2_outerBActiveBoundaryInjection_restrict_to_retainedComplement
      iOldE iLeft iRight jLeft jRight f
      (geometricPieceVertices Old outer) hOldActiveBoundaryInj
  exact fullNativeReplacement_pieceScoped_activeBoundaryInj_transfer
    hOldFree hNewFree f flip
    (Set.range (jLeft.comp iLeft))
    (fullFreeRightExclusiveTarget iRight jRight)
    (geometricPieceVertices Old outer)
    (geometricPieceVertices New newOuter)
    hSameE hOldRootSeam hCarrierSubset hNoNewB hOldScoped

end AllThoseRamseyClasses.Lifts
