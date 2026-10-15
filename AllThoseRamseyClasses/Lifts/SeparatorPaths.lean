import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# Path transport and component separation for nested cuts

These are reusable pure relational graph lemmas for Proposition `prop:sep`
of the 2019 paper. Functional structures use them on their existing
`Structure.graph` reduct, and no closure assumption is needed here.

A smaller cut deletes fewer vertices. Paths avoiding a larger cut
therefore remain valid after shrinking it. Because Gaifman adjacency
is symmetric, the resulting components are genuine disjoint
connected components. The last lemma says that deleting every
neighbour of a component prevents paths from leaving that component.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- View a vertex outside R as a vertex outside a smaller S ⊆ R. -/
def outsideCutMap {R S : Set V} (hSR : S ⊆ R)
    (x : {v : V // v ∉ R}) : {v : V // v ∉ S} :=
  ⟨x.1, fun hx => x.2 (hSR hx)⟩

/-- Monotonicity of paths under shrinking the deleted cut. -/
theorem reachOutside_of_cut_subset (A : RelStructure L V)
    {R S : Set V} (hSR : S ⊆ R)
    (x y : {v : V // v ∉ R})
    (h : ReachOutside A R x y) :
    ReachOutside A S (outsideCutMap hSR x) (outsideCutMap hSR y) := by
  exact (Relation.ReflTransGen.lift (outsideCutMap hSR)
    (fun _ _ hxy => hxy)) h

/-- Gaifman reachability is symmetric (without needing an
implicit symmetric-relation typeclass). -/
theorem reachOutside_symm (A : RelStructure L V) (R : Set V)
    {x y : {v : V // v ∉ R}}
    (h : ReachOutside A R x y) :
    ReachOutside A R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hedge ih =>
      exact (Relation.ReflTransGen.single
        (GaifmanAdjacent.symm hedge)).trans ih

/-- The original connected component is contained in the component
after deleting fewer vertices. No additional vertex identifications. -/
theorem componentFrom_subset_of_cut_subset
    (A : RelStructure L V) {R S : Set V}
    (hSR : S ⊆ R) (root : {v : V // v ∉ R}) :
    componentFrom A R root ⊆
      componentFrom A S (outsideCutMap hSR root) := by
  intro z hz
  obtain ⟨hzR, hpath⟩ := hz
  refine ⟨fun hzS => hzR (hSR hzS), ?_⟩
  exact reachOutside_of_cut_subset A hSR root ⟨z, hzR⟩ hpath

/-- Distinct components are disjoint, expressed directly in terms of
the absence of a path between their roots. -/
theorem componentFrom_disjoint_of_not_reach (A : RelStructure L V)
    (R : Set V) (x y : {v : V // v ∉ R})
    (hxy : ¬ ReachOutside A R x y) :
    Disjoint (componentFrom A R x) (componentFrom A R y) := by
  apply Set.disjoint_left.mpr
  intro z hzX hzY
  have hzx : ReachOutside A R x ⟨z, hzY.1⟩ := by
    simpa using hzX.2
  have hzy : ReachOutside A R ⟨z, hzY.1⟩ y :=
    reachOutside_symm A R hzY.2
  exact hxy (hzx.trans hzy)

/-- A property of vertices propagates along paths outside S if it
is preserved by every surviving Gaifman edge. -/
theorem reachOutside_stays_in
    (A : RelStructure L V) (S C : Set V)
    (root : {v : V // v ∉ S})
    (hroot : root.1 ∈ C)
    (hstep : ∀ {a b : {v : V // v ∉ S}},
      a.1 ∈ C → outsideAdjacency A S a b → b.1 ∈ C)
    {y : {v : V // v ∉ S}}
    (h : ReachOutside A S root y) :
    y.1 ∈ C := by
  induction h with
  | refl => exact hroot
  | tail hpath hedge ih =>
      exact hstep ih hedge

/-- If the removed set S includes the entire external neighbourhood
of C, every path from a vertex of C avoiding S stays inside C. -/
theorem reachOutside_stays_in_avoid_boundary
    (A : RelStructure L V) (S C : Set V)
    (root : {v : V // v ∉ S}) (hroot : root.1 ∈ C)
    (hN : gaifmanNeighborhood A C ⊆ S)
    {y : {v : V // v ∉ S}}
    (h : ReachOutside A S root y) :
    y.1 ∈ C := by
  apply reachOutside_stays_in A S C root hroot ?_ h
  intro a b ha hab
  by_cases hb : b.1 ∈ C
  · exact hb
  have hbN : b.1 ∈ gaifmanNeighborhood A C :=
    ⟨hb, a.1, ha, hab⟩
  exact False.elim (b.2 (hN hbN))

end AllThoseRamseyClasses.Lifts
