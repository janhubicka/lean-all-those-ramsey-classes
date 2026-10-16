import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward

/-!
# Minimal closed separators: the converse and the rooted iff

Complete the pair-of-roots version of Proposition `prop:sep` from
Hubička--Nešetřil, *All those Ramsey classes* (2019).

If a smaller closed cut S separates x and y, the old x-component
and y-component lie in the corresponding components of A minus S.
By the already checked functional lemma, each union
S ∪ component(A minus S) is closed. Thus the old boundary-closure
equations force every vertex of R minus S to lie in BOTH of these
new disjoint components, a contradiction.

The roots x,y represent the two components. The separate
equivalence with the manuscript's quantification over whole
components rather than chosen roots remains a presentational lemma;
no finite carrier, arity bound, or false closure/edge identification
is assumed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The function closure of an old component's neighbourhood belongs
to S together with the larger component obtained on deleting a
smaller closed cut S ⊆ R. -/
theorem boundaryClosure_subset_smallerCutComponent
    (A : Structure L V) {R S : Set V}
    (hSclosed : A.IsClosed S) (hSR : S ⊆ R)
    (root : {v : V // v ∉ R}) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R root))
        ⊆ S ∪ componentFrom A.graph S (outsideCutMap hSR root) := by
  let CR : Set V := componentFrom A.graph R root
  let CS : Set V :=
    componentFrom A.graph S (outsideCutMap hSR root)
  have hSeed : gaifmanNeighborhood A.graph CR ⊆ S ∪ CS := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact Or.inl hzS
    obtain ⟨_, w, hwCR, hwz⟩ := hz
    have hwCS : w ∈ CS :=
      componentFrom_subset_of_cut_subset A.graph hSR root hwCR
    exact Or.inr
      (componentFrom_step A.graph S
        (outsideCutMap hSR root) hwCS hzS hwz)
  have hClosed : A.IsClosed (S ∪ CS) :=
    functionalComponentUnion_isClosed A S hSclosed
      (outsideCutMap hSR root)
  intro z hz
  exact hz (S ∪ CS) hClosed hSeed

/-- The reverse implication of the 2019 minimal separating cut
characterization, for chosen roots of two different components. -/
theorem minimalClosedSeparator_of_bothBoundaries_eq
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R)
    (x y : {v : V // v ∉ R})
    (hxy : ¬ ReachOutside A.graph R x y)
    (hx : A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) = R)
    (hy : A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R y)) = R) :
    IsMinimalClosedSeparator A R x y := by
  refine ⟨hR, hxy, ?_⟩
  intro S hSclosed hSR hNoReach z hzR
  by_contra hzS
  let xS := outsideCutMap hSR x
  let yS := outsideCutMap hSR y
  have hzHullX : z ∈ A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) := by
    rw [hx]
    exact hzR
  have hzHullY : z ∈ A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph R y)) := by
    rw [hy]
    exact hzR
  have hzX : z ∈ componentFrom A.graph S xS := by
    have h := boundaryClosure_subset_smallerCutComponent
      A hSclosed hSR x hzHullX
    exact h.resolve_left hzS
  have hzY : z ∈ componentFrom A.graph S yS := by
    have h := boundaryClosure_subset_smallerCutComponent
      A hSclosed hSR y hzHullY
    exact h.resolve_left hzS
  have hDisjoint : Disjoint
      (componentFrom A.graph S xS)
      (componentFrom A.graph S yS) :=
    componentFrom_disjoint_of_not_reach A.graph S xS yS hNoReach
  exact (Set.disjoint_left.mp hDisjoint) hzX hzY

/-- Exact two-way minimal-separator characterization by generated
closures of both component neighborhoods. This is the fixed-root
form of manuscript Proposition `prop:sep`. -/
theorem minimalClosedSeparator_iff_boundaries_eq
    (A : Structure L V) (R : Set V) (hR : A.IsClosed R)
    (x y : {v : V // v ∉ R})
    (hxy : ¬ ReachOutside A.graph R x y) :
    IsMinimalClosedSeparator A R x y ↔
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph R x)) = R ∧
      A.functionClosure
        (gaifmanNeighborhood A.graph (componentFrom A.graph R y)) = R := by
  constructor
  · exact minimalClosedSeparator_bothBoundaries_eq A R x y
  · rintro ⟨hx, hy⟩
    exact minimalClosedSeparator_of_bothBoundaries_eq
      A R hR x y hxy hx hy

end AllThoseRamseyClasses.Lifts
