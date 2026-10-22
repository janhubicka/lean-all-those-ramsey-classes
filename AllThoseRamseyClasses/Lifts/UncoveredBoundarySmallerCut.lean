import AllThoseRamseyClasses.Lifts.BoundaryClosureExactComponent
import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward

/-!
# An uncovered component-boundary vertex produces a STRICTLY smaller closed cut

In the original Section 3 Claim 2, the difficult source-side
alternative is that the generated boundary of one S-component
is NOT covered by the generated boundary of an opposite
component after deleting a smaller closed cut.

This missing coverage has a definite positive geometric
consequence: if T is a native function-closed separator of
x and y, and some vertex of T is outside the generated
external boundary of the y-component of Source minus T,
then U=Cl(N(component(T,y))) is itself a STRICT proper
function-closed subset of T which still separates x and y.

More precisely, the whole old y-component survives EXACTLY
after shrinking T to U. Hence this is a real source cut
and unchanged connected component, not just a cardinality
inequality or a weak target image.

This is a purely native functional lemma: no forbidden family,
canonical lift, weak EHN map or root-image injection is used.
The fact that the strict smaller cut yields a flippable
sub-piece or contradicts mixed-piece minimality is still open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A missing old-cut boundary vertex on the opposite y-side
supplies the complete closure of that side's external
neighborhood, a strictly SMALLER closed separator U.

The exact y-component in the original forbidden source
is preserved, rather than enlarged by the smaller cut.
The output provides the actual proof U ⊆ T to transport
both chosen source vertices into Source minus U. -/
theorem uncoveredBoundary_hasStrictSmallerClosedSeparator
    (A : Structure L V)
    (T : Set V)
    (hClosed : A.IsClosed T)
    (x y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside A.graph T x y)
    (hUncovered : ¬ T ⊆
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y))) :
    ∃ (U : Set V) (hUT : U ⊆ T),
      A.IsClosed U ∧
      U ⊂ T ∧
      ¬ ReachOutside A.graph U
        (outsideCutMap hUT x) (outsideCutMap hUT y) ∧
      componentFrom A.graph U (outsideCutMap hUT y) =
        componentFrom A.graph T y := by
  let U : Set V :=
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  let hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut A T hClosed y
  have hClosedU : A.IsClosed U :=
    A.functionClosure_isClosed
      (gaifmanNeighborhood A.graph (componentFrom A.graph T y))
  have hStrict : U ⊂ T := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hUT, ?_⟩
    intro hEq
    apply hUncovered
    intro z hzT
    change z ∈ U
    rw [hEq]
    exact hzT
  have hSepYX : ¬ ReachOutside A.graph T y x := by
    intro hPath
    exact hSep (reachOutside_symm A.graph T hPath)
  have hSepUYX : ¬ ReachOutside A.graph U
      (outsideCutMap hUT y) (outsideCutMap hUT x) :=
    closureNeighborhood_separates A T hClosed y x hSepYX
  have hSepUXY : ¬ ReachOutside A.graph U
      (outsideCutMap hUT x) (outsideCutMap hUT y) := by
    intro hPath
    exact hSepUYX (reachOutside_symm A.graph U hPath)
  have hExact : componentFrom A.graph U (outsideCutMap hUT y) =
      componentFrom A.graph T y :=
    componentBoundaryClosure_preserves_exact_component
      A T hClosed y
  exact ⟨U, hUT, hClosedU, hStrict, hSepUXY, hExact⟩

end AllThoseRamseyClasses.Lifts
