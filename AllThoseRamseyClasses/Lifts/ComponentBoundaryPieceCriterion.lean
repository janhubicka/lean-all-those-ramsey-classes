import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart

/-!
# Exact boundary criterion for a source component to be a genuine piece

Let S be function-closed, let C be the actual component of x
outside S, and let T=Cl(N(C)), contained in S. The checked
boundary-component theorem proves C is still precisely the
component of x after deleting T.

The root T is an inclusion-minimal CLOSED separator between x
and SOME other vertex y if and only if there exists a second
T-component D with D disjoint from C and with Cl(N(D))=T.

This is an EXACT criterion, not just the sufficient special case
where another original S-component has the same boundary.
For example, shrinking S to T may add old S-vertices to D,
making its new external boundary T even when its original
S-component boundary is different.

The verified converse of Proposition prop:sep gives the backward
direction; its forward direction gives the necessity. Under
finite source cardinality, a partner D produces a genuine
GeometricFunctionalPieceData with full root T and selected
nonroot component exactly C.

No global weak-map injectivity, forbidden image quotient, or
unproved flippability hypothesis enters these geometric facts.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Exact source-geometric test for when the generated boundary
T of an S-component C is itself a minimal closed separator root.
A partner after deleting T must be in a different component and
have the SAME complete generated functional neighborhood boundary.

The root T and its inclusion in S are explicit arguments,
avoiding any choice of an unspecified minimal separator. -/
theorem componentBoundary_hasMinimalPiece_iff_partner
    (A : Structure L V) (S T : Set V)
    (hS : A.IsClosed S)
    (x : {v : V // v ∉ S})
    (hT : T =
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)))
    (hTS : T ⊆ S) :
    (∃ y : {v : V // v ∉ T},
      IsMinimalClosedSeparator A T (outsideCutMap hTS x) y) ↔
    (∃ y : {v : V // v ∉ T},
      ¬ ReachOutside A.graph T (outsideCutMap hTS x) y ∧
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph T y)) = T) := by
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  have hClosedT : A.IsClosed T := by
    rw [hT]
    exact A.functionClosure_isClosed
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
  have hCx :
      componentFrom A.graph T xT =
        componentFrom A.graph S x := by
    subst T
    simpa only using
      (componentBoundaryClosure_preserves_exact_component A S hS x)
  have hXBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph T xT)) =
      T := by
    rw [hCx]
    exact hT.symm
  constructor
  · rintro ⟨y, hMin⟩
    exact ⟨y, hMin.2.1,
      (minimalClosedSeparator_bothBoundaries_eq A T xT y hMin).2⟩
  · rintro ⟨y, hSep, hYBoundary⟩
    exact ⟨y,
      minimalClosedSeparator_of_bothBoundaries_eq
        A T hClosedT xT y hSep hXBoundary hYBoundary⟩

/-- A FINITE source component with a genuine boundary partner
can be turned into an ACTUAL function-closed minimal-separator
piece: enumerate all root vertices of T with no repetitions.
The selected nonroot component is exactly C, not a larger
component created when the cut shrinks.

This is a source-side geometric certificate, not yet a target
EHN factorization or a global-canonical-lift flip. -/
theorem finite_componentBoundary_hasGeometricPiece_of_partner
    [Finite V]
    (A : Structure L V) (S T : Set V)
    (hS : A.IsClosed S)
    (x : {v : V // v ∉ S})
    (hT : T =
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph S x)))
    (hTS : T ⊆ S)
    (y : {v : V // v ∉ T})
    (hSep : ¬ ReachOutside A.graph T (outsideCutMap hTS x) y)
    (hYBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph T y)) = T) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData A n),
      Set.range d.roots = T ∧
      Set.range d.roots ⊆ S ∧
      d.left.1 = x.1 ∧ d.right.1 = y.1 ∧
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph S x := by
  -- Construct the selected minimal separator directly for
  -- this specified partner, without losing its identity to
  -- existential choice.
  have hClosedT : A.IsClosed T := by
    rw [hT]
    exact A.functionClosure_isClosed
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
  have hCx :
      componentFrom A.graph T (outsideCutMap hTS x) =
        componentFrom A.graph S x := by
    subst T
    simpa only using
      (componentBoundaryClosure_preserves_exact_component A S hS x)
  have hXBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T (outsideCutMap hTS x))) = T := by
    rw [hCx]
    exact hT.symm
  have hMin' : IsMinimalClosedSeparator A T
      (outsideCutMap hTS x) y :=
    minimalClosedSeparator_of_bothBoundaries_eq
      A T hClosedT (outsideCutMap hTS x) y hSep
      hXBoundary hYBoundary
  obtain ⟨n, d, hRoot, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart
      A T (outsideCutMap hTS x) y hMin'
  have hComp :
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph S x := by
    -- First transport the whole dependent subtype along the
    -- chart's literal root-set equality. An ordinary rw is
    -- insufficient because the type of d.left depends on it.
    cases hRoot
    have hLeftEq : d.left = outsideCutMap hTS x :=
      Subtype.ext hLeft
    rw [hLeftEq]
    exact hCx
  exact ⟨n, d, hRoot, by simpa only [hRoot] using hTS,
    hLeft, hRight, hComp⟩

end AllThoseRamseyClasses.Lifts
