import AllThoseRamseyClasses.Lifts.FullFreeAmalgamExteriorOldRoot
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart

/-!
# Exact surviving outer-root criterion after a native inner flip

The published Section 3 Claim 2 replaces an inner B-only rooted
piece inside a mixed outer source piece. Its full native complement
and the original outer-root coordinates survive. But this alone
does NOT show that the same old root is an inclusion-minimal closed
separator of the replacement forbidden source.

The verified exterior-preservation theorem handles precisely the
component C on the unchanged complement side, even when the old
outer root T does not contain the inner gluing seam. It transports
the WHOLE component and its generated functional neighborhood
boundary Cl(N(C)) = T.

Here we identify the EXACT remaining source-geometric condition:
choose any opposite vertex y outside the transported old root and
the preserved exterior component. Then the transported old root
is a genuine inclusion-minimal function-closed separator of the
preserved exterior and y **if and only if** the generated
neighborhood boundary of the new y-component is the whole old root.

The forward implication is the checked minimal-closed-separator
boundary theorem; the reverse implication uses the already
checked converse. For finite new forbidden-source carriers, this
produces a literal native geometric piece with the complete
transported old root, not merely an arbitrary closed context.

No arbitrary forbidden weak EHN map is assumed injective, and
no image quotient is substituted for a true source structure.
The opposite-boundary premise remains unproved in the general
2019 Claim 2: it is exactly the missing interior component
invariant under a contextual B-to-A flip. No unrestricted
strong amalgamation or Ramsey theorem is claimed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Once the old exterior component of a full native functional
free amalgam survives with its exact original boundary T, the
transported root iR(T) is a MINIMAL CLOSED separator of that
exterior and a specified opposite vertex y exactly when the
opposite component also has generated boundary iR(T).

The inner gluing seam need NOT lie inside the old root T. The
hypothesis on y only says it is genuinely in another component
of the replacement source after deleting the old root. -/
theorem fullFreeAmalgam_outerOldRoot_minimal_iff_oppositeBoundary
    {H E F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (T : Set F) (hTclosed : Right.IsClosed T)
    (x : {b : F // b ∉ T})
    (hPrivate :
      componentFrom Right.graph T x ⊆ {b : F | b ∉ Set.range sR})
    (hExteriorBoundary :
      Right.functionClosure
        (gaifmanNeighborhood Right.graph
          (componentFrom Right.graph T x)) = T)
    (y : {w : W // w ∉ iR '' T})
    (hyOpposite :
      y.1 ∉ iR '' componentFrom Right.graph T x) :
    IsMinimalClosedSeparator Whole (iR '' T)
      (fullFunctionalEmbedding_outsideCut iR T x) y ↔
    Whole.functionClosure
      (gaifmanNeighborhood Whole.graph
        (componentFrom Whole.graph (iR '' T) y)) = iR '' T := by
  have hExterior :=
    fullFreeAmalgam_exteriorComponent_preserved_at_oldRoot
      hFree T x hPrivate hExteriorBoundary
  have hClosed : Whole.IsClosed (iR '' T) :=
    functionalEmbedding_image_closed Right Whole iR T hTclosed
  have hSep : ¬ ReachOutside Whole.graph (iR '' T)
      (fullFunctionalEmbedding_outsideCut iR T x) y := by
    intro hPath
    have hyC : y.1 ∈ componentFrom Whole.graph (iR '' T)
        (fullFunctionalEmbedding_outsideCut iR T x) :=
      ⟨y.2, hPath⟩
    rw [hExterior.1] at hyC
    exact hyOpposite hyC
  constructor
  · intro hMin
    exact (minimalClosedSeparator_bothBoundaries_eq
      Whole (iR '' T)
      (fullFunctionalEmbedding_outsideCut iR T x) y hMin).2
  · intro hInteriorBoundary
    exact minimalClosedSeparator_of_bothBoundaries_eq
      Whole (iR '' T) hClosed
      (fullFunctionalEmbedding_outsideCut iR T x) y hSep
      hExterior.2 hInteriorBoundary

/-- If an actual finite new source additionally has one opposite
component with the same generated boundary as its preserved
exterior component, then the transported original root is the
COMPLETE root of an actual geometric minimal-separator piece.

This is the exact geometric half of the contextual Claim 2
invariant. In particular the new root is NOT constructed by an
unsupported quotient or by silently replacing the original
set-valued functional language with its graph encoding. -/
theorem finite_outerOldRoot_hasGeometricPiece_of_oppositeBoundary
    {H E F W : Type v} [Finite W]
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (T : Set F) (hTclosed : Right.IsClosed T)
    (x : {b : F // b ∉ T})
    (hPrivate :
      componentFrom Right.graph T x ⊆ {b : F | b ∉ Set.range sR})
    (hExteriorBoundary :
      Right.functionClosure
        (gaifmanNeighborhood Right.graph
          (componentFrom Right.graph T x)) = T)
    (y : {w : W // w ∉ iR '' T})
    (hyOpposite :
      y.1 ∉ iR '' componentFrom Right.graph T x)
    (hInteriorBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph (iR '' T) y)) = iR '' T) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Whole n),
      Set.range d.roots = iR '' T ∧
      d.left.1 = iR x.1 ∧ d.right.1 = y.1 ∧
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph
            (Set.range d.roots) d.left)) = iR '' T := by
  have hMin : IsMinimalClosedSeparator Whole (iR '' T)
      (fullFunctionalEmbedding_outsideCut iR T x) y :=
    (fullFreeAmalgam_outerOldRoot_minimal_iff_oppositeBoundary
      hFree T hTclosed x hPrivate hExteriorBoundary y
      hyOpposite).2 hInteriorBoundary
  obtain ⟨n, d, hRoot, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart
      Whole (iR '' T)
      (fullFunctionalEmbedding_outsideCut iR T x) y hMin
  have hSelectedBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph
            (Set.range d.roots) d.left)) = iR '' T := by
    have hBoundaries :=
      minimalClosedSeparator_bothBoundaries_eq Whole
        (Set.range d.roots) d.left d.right d.minimal
    exact hBoundaries.1.trans hRoot
  exact ⟨n, d, hRoot, hLeft, hRight, hSelectedBoundary⟩

end AllThoseRamseyClasses.Lifts
