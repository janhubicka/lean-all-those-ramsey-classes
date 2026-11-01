import AllThoseRamseyClasses.Lifts.FullFreeAmalgamOuterOldRootCriterion

/-!
# Track C: recover the prescribed original order of a transported geometric root

Track A's native minimal-separator criterion produces an ACTUAL
geometric piece with its complete root SET, but the finite
enumeration of that set can differ from the ordered root tuple
whose original target coordinates are preserved under the flip.

The 2019 canonical-lift relation is an ORDERED relation of arity n.
A mere equality of finite root sets is therefore not enough to
identify the original canonical relation or the fixed-root chart.

This lemma reenumerates an actual geometric minimal-cut piece by
ANY prescribed injective tuple with the SAME literal cut set. It
retains the two selected source vertices and their original
minimal closed separator proof. No weak EHN map or induced-target
injectivity is involved.

The remaining Track A prerequisite is geometric recognition of
the transported context; reordering alone does not supply it.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Replace the enumeration of a genuine minimal closed
separator by any other injective root tuple with exactly the
same range. The resulting data remain a genuine source-geometric
piece and select the very same two source vertices.

This is the ordered-root normalization required between the
un-ordered existence statement in Track A and the exact indexed
canonical lift used by Track C. -/
theorem geometricPiece_reenumerate_sameClosedCut
    (A : Structure L V)
    {m n : ℕ}
    (d : GeometricFunctionalPieceData A m)
    (newRoots : Fin n → V)
    (hInjective : Function.Injective newRoots)
    (hSameCut : Set.range newRoots = Set.range d.roots) :
    ∃ e : GeometricFunctionalPieceData A n,
      e.roots = newRoots ∧
      Set.range e.roots = Set.range d.roots ∧
      e.left.1 = d.left.1 ∧
      e.right.1 = d.right.1 := by
  let left : {v : V // v ∉ Set.range newRoots} :=
    ⟨d.left.1, by simpa only [hSameCut] using d.left.2⟩
  let right : {v : V // v ∉ Set.range newRoots} :=
    ⟨d.right.1, by simpa only [hSameCut] using d.right.2⟩
  have hMinimal :
      IsMinimalClosedSeparator A (Set.range newRoots) left right := by
    simpa only [hSameCut] using d.minimal
  let e : GeometricFunctionalPieceData A n := {
    roots := newRoots
    roots_injective := hInjective
    left := left
    right := right
    minimal := hMinimal
  }
  exact ⟨e, rfl, hSameCut, rfl, rfl⟩

/-- Specialize the verified opposite-generated-boundary criterion to
the EXACT old ordered root tuple, rather than accepting the arbitrary
finite enumeration returned by the existential chart constructor.

This statement is conditional only on the same opposite boundary
already isolated by Track A. It makes the ordered-root part of
Track C's source-geometric handoff available with NO additional
root permutation or weakened (un-ordered) canonical relation. -/
theorem finite_outerOldRoot_hasGeometricPiece_withPrescribedRoots
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
          (componentFrom Whole.graph (iR '' T) y)) = iR '' T)
    {n : ℕ}
    (newRoots : Fin n → W)
    (hRootInjective : Function.Injective newRoots)
    (hSameRoot : Set.range newRoots = iR '' T) :
    ∃ d : GeometricFunctionalPieceData Whole n,
      d.roots = newRoots ∧
      Set.range d.roots = iR '' T ∧
      d.left.1 = iR x.1 ∧ d.right.1 = y.1 ∧
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph (Set.range d.roots) d.left)) =
            iR '' T := by
  obtain ⟨m, d, hRoots, hLeft, hRight, _hBoundary⟩ :=
    finite_outerOldRoot_hasGeometricPiece_of_oppositeBoundary
      hFree T hTclosed x hPrivate hExteriorBoundary y
      hyOpposite hInteriorBoundary
  obtain ⟨e, hERoots, hECut, hELeft, hERight⟩ :=
    geometricPiece_reenumerate_sameClosedCut
      Whole d newRoots hRootInjective
      (hSameRoot.trans hRoots.symm)
  refine ⟨e, hERoots, hECut.trans hRoots,
    hELeft.trans hLeft, hERight.trans hRight, ?_⟩
  exact (geometricPiece_left_boundary_closure Whole e).trans
    (hECut.trans hRoots)

end AllThoseRamseyClasses.Lifts
