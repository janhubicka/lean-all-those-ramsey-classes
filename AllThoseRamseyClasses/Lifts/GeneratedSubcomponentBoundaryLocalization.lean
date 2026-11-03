import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent
import AllThoseRamseyClasses.Lifts.GeneratedInnerRootOuterCutAttachment

/-!
# Boundary localization for a subcomponent of a closed-cut component

Let C be a complete Gaifman component of A after deleting a
function-closed cut T, and D any subset of C. Then every vertex
of the GENERATED boundary Cl(N(D)) which lies in T already lies
in the GENERATED boundary Cl(N(C)).

This is not immediate for native partial functions: closure can
create vertices of T that are not direct neighbours of D.

The proof reduces the original cut T to its exact generated
boundary R=Cl(N(C)), which is a closed subset of T. The entire
component C survives deleting R (verified boundary reduction).
The verified generated-boundary attachment lemma then shows
Cl(N(D)) lies inside R union C. Intersecting with T removes C.

This reusable LOCAL result is independent of the actual source
flip, EHN target-map injectivity, forbidden-family regularity,
and any rooted profile equivalence. It will be used to recover
the complete older outer boundary after the new component is
identified in Track A.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Inside a complete component C of the complement of a CLOSED cut
T, the T-part of the entire GENERATED neighbourhood boundary of
any D subset C lies in the GENERATED boundary of C itself.

This works with arbitrary native function arities, nullary outputs,
and higher-arity Gaifman incidences. No minimality of T is assumed. -/
theorem generatedSubcomponentBoundary_inter_cut_subset_componentBoundary
    (A : Structure L V) (T : Set V) (hT : A.IsClosed T)
    (x : {v : V // v ∉ T}) (D : Set V)
    (hD : D ⊆ componentFrom A.graph T x)
    (z : V)
    (hz : z ∈ A.functionClosure
      (gaifmanNeighborhood A.graph D))
    (hzT : z ∈ T) :
    z ∈ A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T x)) := by
  let C : Set V := componentFrom A.graph T x
  let R : Set V :=
    A.functionClosure (gaifmanNeighborhood A.graph C)
  have hRC := componentBoundaryClosure_closed_subset_cut A T hT x
  have hRclosed : A.IsClosed R := hRC.1
  have hRsubset : R ⊆ T := hRC.2
  let xr : {v : V // v ∉ R} := outsideCutMap hRsubset x
  have hComponent : componentFrom A.graph R xr = C := by
    simpa only [R, C, xr] using
      (componentBoundaryClosure_preserves_exact_component A T hT x)
  have hDsmall : D ⊆ componentFrom A.graph R xr := by
    intro y hy
    rw [hComponent]
    exact hD hy
  have hBound : A.functionClosure
      (gaifmanNeighborhood A.graph D) ⊆
        R ∪ componentFrom A.graph R xr :=
    functionalBoundaryClosure_subset_cutUnionComponent
      A R hRclosed xr D hDsmall
  rcases hBound hz with hzR | hzComp
  · exact hzR
  · have hzC : z ∈ C := by
      rw [hComponent] at hzComp
      exact hzComp
    have hDisj : Disjoint C T :=
      componentFrom_disjoint_cut A.graph T x
    exact False.elim ((Set.disjoint_left.mp hDisj) hzC hzT)

end AllThoseRamseyClasses.Lifts
