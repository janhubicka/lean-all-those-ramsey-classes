import AllThoseRamseyClasses.Lifts.Claim2ClosedContextNoEscape
import AllThoseRamseyClasses.Lifts.ComponentBoundaryPieceCriterion

/-!
# Track C: a proper one-sided geometric subpiece inside a NON-geometric context

A literal contextual B→A flip yields an outer set K' that is
native function-closed and preserves its rooted forbidden
incompatibility profile and exact support counts. It is not
automatically a genuine minimal-closed-separator piece.

The alternative no-escape invariant says no Gaifman edge leaves
K' from a vertex of K' outside the shared target-root preimage S.
This is enough to construct an actual proper B-only inner
GEOMETRIC piece, without supposing K' itself is geometric:

* any chosen S-component B starting inside K' stays inside K';
* its complete generated boundary T=Cl(N(B)) lies inside S∩K';
* if an opposite boundary partner exists, the standard finite
  source theorem constructs a genuine minimal-separator piece d
  with entire selected component exactly B and entire root T;
* an A-only vertex a inside K' but outside S witnesses that
  this new d is PROPER in K';
* injectivity on selected T is enough for injective target
  coordinates on d's complete ordered root.

This source result does not require a minimal old outer root
or a minimal LEFT-support witness. It is the geometric selection
half of a possible revised iteration on arbitrary closed
no-escape contexts; the full canonical flip and profile
transport remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A finite source's arbitrary CLOSED NO-ESCAPE context contains
a genuine proper one-sided native geometric piece whenever one
of its S-components has a nonempty complete generated boundary
T with a genuine opposite boundary partner.

The piece is in the original source itself. Its entire selected
nonroot component is exactly the original S-component, not an
uncontrolled extension after shrinking the cut. No source
A-support minimality or weak target-map injection outside T. -/
theorem functionalNoEscape_properOneSidedGeometricSubpiece_of_partner
    [Finite V]
    (A : Structure L V)
    (S K : Set V)
    (hSclosed : A.IsClosed S)
    (hKclosed : A.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam A S K)
    (x : {v : V // v ∉ S})
    (hxK : x.1 ∈ K)
    (AOnly : Set V)
    (hBNoA : ∀ z : V,
      z ∈ componentFrom A.graph S x → z ∉ AOnly)
    (a : V) (haK : a ∈ K)
    (haNotS : a ∉ S) (haAOnly : a ∈ AOnly)
    (T : Set V)
    (hT : T = A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x)))
    (hTS : T ⊆ S)
    (hTnonempty : T.Nonempty)
    (y : {v : V // v ∉ T})
    (hSep : ¬ ReachOutside A.graph T (outsideCutMap hTS x) y)
    (hYBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)) = T)
    {W : Type v} (f : V → W)
    (hInjT : Set.InjOn f T) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData A m),
      0 < m ∧
      Set.range d.roots = T ∧
      Set.range d.roots ⊆ S ∩ K ∧
      geometricPieceVertices A d ⊂ K ∧
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph S x ∧
      (∀ z : V,
        z ∈ functionalComponentFrom A
          (Set.range d.roots) d.left → z ∉ AOnly) ∧
      Function.Injective (fun i : Fin m => f (d.roots i)) := by
  classical
  have hCompInside : componentFrom A.graph S x ⊆ K :=
    functionalNoEscape_wholeComponent_insideContext
      A S K hNoEscape x hxK
  have hTInside : T ⊆ S ∩ K := by
    intro z hz
    exact functionalNoEscape_component_generatedBoundary_inside
      A S K hSclosed hKclosed hNoEscape x hxK
      (by simpa only [hT] using hz)
  obtain ⟨m, d, hRootT, _hRootS, _hLeft, _hRight, hCompEq⟩ :=
    finite_componentBoundary_hasGeometricPiece_of_partner
      A S T hSclosed x hT hTS y hSep hYBoundary
  have hDRootInside : Set.range d.roots ⊆ S ∩ K := by
    intro z hz
    exact hTInside (by simpa only [hRootT] using hz)
  have hPieceInside : geometricPieceVertices A d ⊆ K := by
    intro z hz
    rcases hz with hzRoot | hzComponent
    · exact (hDRootInside hzRoot).2
    · apply hCompInside
      simpa only [hCompEq] using hzComponent
  have haNotD : a ∉ geometricPieceVertices A d := by
    intro haD
    rcases haD with haRoot | haComponent
    · exact haNotS (hDRootInside haRoot).1
    · have haB : a ∈ componentFrom A.graph S x := by
        simpa only [hCompEq] using haComponent
      exact hBNoA a haB haAOnly
  have hProper : geometricPieceVertices A d ⊂ K := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hPieceInside, ?_⟩
    intro hEq
    exact haNotD (hEq.symm ▸ haK)
  have hNoA : ∀ z : V,
      z ∈ functionalComponentFrom A
        (Set.range d.roots) d.left → z ∉ AOnly := by
    intro z hz
    apply hBNoA z
    simpa only [hCompEq] using hz
  have hRootInj : Function.Injective
      (fun i : Fin m => f (d.roots i)) := by
    intro i j hij
    apply d.roots_injective
    exact hInjT
      (by simpa only [hRootT] using
        (show d.roots i ∈ Set.range d.roots from ⟨i, rfl⟩))
      (by simpa only [hRootT] using
        (show d.roots j ∈ Set.range d.roots from ⟨j, rfl⟩))
      hij
  have hm : 0 < m := by
    obtain ⟨t, ht⟩ := hTnonempty
    have htD : t ∈ Set.range d.roots := by
      simpa only [hRootT] using ht
    obtain ⟨i, _hi⟩ := htD
    cases m with
    | zero => exact Fin.elim0 i
    | succ k => exact Nat.zero_lt_succ k
  exact ⟨m, d, hm, hRootT, hDRootInside,
    hProper, hCompEq, hNoA, hRootInj⟩

end AllThoseRamseyClasses.Lifts
