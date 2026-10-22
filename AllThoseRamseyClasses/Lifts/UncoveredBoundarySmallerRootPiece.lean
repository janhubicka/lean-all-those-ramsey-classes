import AllThoseRamseyClasses.Lifts.UncoveredBoundarySmallerCut
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Uncovered source boundary gives a GENUINE smaller-root geometric piece

The previous native functional lemma proves that a missing
opposite-component boundary vertex shrinks a separating
closed cut T to a STRICT proper closed separator U, preserving
the opposite component exactly. In a finite source, choose an
inclusion-minimal closed separator R INSIDE U, and enumerate it
by a distinct ordered root tuple. This gives an actual
GeometricFunctionalPieceData whose root is STRICTLY contained
in the original T and whose distinguished vertices are the
ORIGINAL chosen source vertices.

When the source vertices are joined by a full Gaifman path,
the new root width is positive, as required by the original
global quotient-indexed piece language.

The conclusion does NOT assert that this NEW minimal-root
piece is contained inside an old selected outer piece,
that its selected component remains monochromatic, or
that its weak target root images are injective. Those are
the remaining essential conditions for a Claim 2 flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Failure of full generated boundary coverage on the
opposite y-side of a native function-closed separator T
produces an actual POSITIVE-width minimal geometric source
piece rooted strictly INSIDE T.

There is no forbidden-image normalization and no arbitrary
choice of a nonclosed root. The exact selected pair of
source vertices is preserved. -/
theorem finite_uncoveredBoundary_hasSmallerRootGeometricPiece
    [Finite V]
    (A : Structure L V)
    (T : Set V)
    (hClosed : A.IsClosed T)
    (x y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside A.graph T x y)
    (hUncovered : ¬ T ⊆
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)))
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData A n),
      0 < n ∧
      Set.range d.roots ⊂ T ∧
      d.left.1 = y.1 ∧ d.right.1 = x.1 := by
  obtain ⟨U, hUT, hClosedU, hStrict, hSepU, _hExact⟩ :=
    uncoveredBoundary_hasStrictSmallerClosedSeparator
      A T hClosed x y hSep hUncovered
  have hSepUYX : ¬ ReachOutside A.graph U
      (outsideCutMap hUT y) (outsideCutMap hUT x) := by
    intro hPath
    exact hSepU (reachOutside_symm A.graph U hPath)
  obtain ⟨R, hRU, hMin⟩ :=
    finite_exists_minimalClosedSeparator_inside
      A U hClosedU
      (outsideCutMap hUT y) (outsideCutMap hUT x) hSepUYX
  have hRT : R ⊆ T := Set.Subset.trans hRU hUT
  have hRneq : R ≠ T := by
    intro hEq
    have hTsubsetU : T ⊆ U := by
      intro z hzT
      apply hRU
      rw [hEq]
      exact hzT
    have hUTeq : U = T := Set.Subset.antisymm hUT hTsubsetU
    exact (Set.ssubset_iff_subset_ne.mp hStrict).2 hUTeq
  have hRstrict : R ⊂ T :=
    Set.ssubset_iff_subset_ne.mpr ⟨hRT, hRneq⟩
  obtain ⟨n, d, hRoot, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart A R
      (outsideCutMap hRU (outsideCutMap hUT y))
      (outsideCutMap hRU (outsideCutMap hUT x)) hMin
  have hLeftOriginal : d.left.1 = y.1 := hLeft
  have hRightOriginal : d.right.1 = x.1 := hRight
  have hPathD : ReachOutside A.graph (∅ : Set V)
      (⟨d.left.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    rw [hLeftOriginal, hRightOriginal]
    exact reachOutside_symm A.graph (∅ : Set V) hConnected
  have hPos : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path A d hPathD
  have hRootProper : Set.range d.roots ⊂ T := by
    rw [hRoot]
    exact hRstrict
  exact ⟨n, d, hPos, hRootProper,
    hLeftOriginal, hRightOriginal⟩

end AllThoseRamseyClasses.Lifts
