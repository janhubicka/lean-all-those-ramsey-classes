import AllThoseRamseyClasses.Lifts.MinimalSeparatorReverse

/-!
# Generated inner separator roots attach to the surviving outer component

Suppose T is a function-closed source cut and C is an actual
Gaifman component after deleting T. Let D be a subset of C.

Every external neighbour of D either lies in T or still belongs
to C: if it lies outside T, one Gaifman edge from D extends
reachability within C. Because T union C is NATIVE function-closed,
the whole generated functional boundary Cl(N(D)) lies inside T∪C.

In particular, if D is the selected component of a genuine inner
piece whose complete function-closed root is
  U = Cl(N(D)),
then ALL root vertices of U outside the old cut T are in that
same surviving C. This is the key connective attachment property
needed when replacing an inner B-only piece of an old mixed
outer piece. It works for arbitrary original set-valued function
arities, including nullary functions (whose generated values
belong to every function-closed T).

This theorem is stronger than a graph-only direct-neighbour
statement: generated closure vertices need not themselves be
neighbours of D. It does not require T⊆U, does not infer any
injectivity for a weak forbidden EHN map and does not assume
the replacement is itself a forbidden source.

What remains for a full 2019 Claim 2 outer-context restoration is
to prove that the inserted selected component D' lies in the
appropriate outer T-component and that the retained old interior
vertices join it, and then preserve the complete opposite
boundary / incompatibility profile.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- An arbitrary source subset D of a T-component has its entire
GENERATED external Gaifman boundary inside the union of the
same component and the closed cut T. The closure may contain
vertices not directly adjacent to D, so the final step uses
native function-closedness rather than graph path locality. -/
theorem functionalBoundaryClosure_subset_cutUnionComponent
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x : {v : V // v ∉ T})
    (D : Set V)
    (hD : D ⊆ componentFrom A.graph T x) :
    A.functionClosure (gaifmanNeighborhood A.graph D) ⊆
      T ∪ componentFrom A.graph T x := by
  let C : Set V := componentFrom A.graph T x
  have hSeed : gaifmanNeighborhood A.graph D ⊆ T ∪ C := by
    intro z hz
    by_cases hzT : z ∈ T
    · exact Or.inl hzT
    · obtain ⟨_, d, hdD, hEdge⟩ := hz
      exact Or.inr
        (componentFrom_step A.graph T x (hD hdD) hzT hEdge)
  have hClosed : A.IsClosed (T ∪ C) :=
    functionalComponentUnion_isClosed A T hTclosed x
  intro z hz
  exact hz (T ∪ C) hClosed hSeed

/-- When U is exactly the GENERATED boundary of an inner selected
component D, and D stays connected to x outside the older closed
outer cut T, every vertex of U not deleted by T lies in that
SAME outer Gaifman component. No inclusion T⊆U or U⊆T. -/
theorem generatedInnerRoot_outsideClosedOuterCut_attaches
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x : {v : V // v ∉ T})
    (D U : Set V)
    (hD : D ⊆ componentFrom A.graph T x)
    (hGeneratedRoot :
      A.functionClosure (gaifmanNeighborhood A.graph D) = U) :
    U \ T ⊆ componentFrom A.graph T x := by
  have hHull := functionalBoundaryClosure_subset_cutUnionComponent
    A T hTclosed x D hD
  intro z hz
  have hzHull : z ∈ A.functionClosure
      (gaifmanNeighborhood A.graph D) := by
    rw [hGeneratedRoot]
    exact hz.1
  exact (hHull hzHull).resolve_left hz.2

/-- A native inner minimal closed separator U always equals the
generated external boundary of its selected component. Therefore
any selected inner component D sitting inside the surviving
outer T-component pulls EVERY U-root vertex outside T into
that component. This is a fully geometric consequence of the
existing verified 2019 Proposition prop:sep, independent of F. -/
theorem minimalInnerRoot_outsideClosedOuterCut_attaches
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    (x : {v : V // v ∉ T})
    {U : Set V}
    (a b : {v : V // v ∉ U})
    (hMin : IsMinimalClosedSeparator A U a b)
    (hD :
      componentFrom A.graph U a ⊆
        componentFrom A.graph T x) :
    U \ T ⊆ componentFrom A.graph T x := by
  have hBoundary :=
    (minimalClosedSeparator_bothBoundaries_eq
      A U a b hMin).1
  exact generatedInnerRoot_outsideClosedOuterCut_attaches
    A T hTclosed x (componentFrom A.graph U a) U
    hD hBoundary

end AllThoseRamseyClasses.Lifts
