import AllThoseRamseyClasses.Lifts.PieceEquivalence

/-!
# Gaifman components after removing a vertex cut

The relational core of Observation `cuty` from Section 3
("Pieces of structures") of *All those Ramsey classes* (2019).

A Gaifman edge is witnessed by a positive relation tuple containing
both DISTINCT vertices. Remove a set R, restrict edges to the surviving
subtype, and take the reflexive/transitive path relation. This yields
actual connected components rather than arbitrary connected subsets.

The proof that the neighbourhood of a component is contained in R
does not require connectedness of the entire ambient graph, finiteness
or minimality of R. For a language with functions, the paper additionally
requires cuts and induced pieces to be *closed*. That is explicitly not
claimed by this relational module; the closure operation will be a
separate layer.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Adjacent *distinct* vertices of the Gaifman graph. Relations with
repeated coordinates and nullary symbols are allowed in the language. -/
def GaifmanAdjacent (A : RelStructure L V) (x y : V) : Prop :=
  x ≠ y ∧
    ∃ (s : L.Symbol) (t : Fin (L.arity s) → V)
      (i j : Fin (L.arity s)),
      A.rel s t ∧ t i = x ∧ t j = y

/-- Every Gaifman edge can be traversed in either direction. -/
theorem GaifmanAdjacent.symm {A : RelStructure L V}
    {x y : V} (h : GaifmanAdjacent A x y) :
    GaifmanAdjacent A y x := by
  obtain ⟨hne, s, t, i, j, ht, hxi, hyj⟩ := h
  exact ⟨Ne.symm hne, s, t, j, i, ht, hyj, hxi⟩

/-- A Gaifman edge lies in one irreducibility witness tuple, and
the converse requires distinct endpoints. -/
theorem GaifmanAdjacent_iff {A : RelStructure L V}
    (x y : V) :
    GaifmanAdjacent A x y ↔
      x ≠ y ∧ ∃ (s : L.Symbol) (t : Fin (L.arity s) → V)
      (i j : Fin (L.arity s)), A.rel s t ∧ t i = x ∧ t j = y := Iff.rfl

/-- The adjacency relation on the vertices remaining after removing
R. This type discipline prevents paths from passing through R. -/
def outsideAdjacency (A : RelStructure L V) (R : Set V) :
    {x : V // x ∉ R} → {x : V // x ∉ R} → Prop :=
  fun x y => GaifmanAdjacent A x.1 y.1

/-- A path in the Gaifman graph avoiding the cut R, including the
zero-length path. -/
def ReachOutside (A : RelStructure L V) (R : Set V)
    (x y : {v : V // v ∉ R}) : Prop :=
  Relation.ReflTransGen (outsideAdjacency A R) x y

/-- The whole connected component of a selected vertex outside R,
expressed back as a subset of the original carrier. -/
def componentFrom (A : RelStructure L V) (R : Set V)
    (root : {v : V // v ∉ R}) : Set V :=
  {x | ∃ hx : x ∉ R,
    ReachOutside A R root ⟨x, hx⟩}

/-- A genuine component of A after removing R is the reachable
set of some surviving root. -/
def IsComponentOutside (A : RelStructure L V) (R C : Set V) : Prop :=
  ∃ root : {v : V // v ∉ R}, C = componentFrom A R root

/-- The selected root belongs to its own component. -/
theorem componentFrom_root (A : RelStructure L V) (R : Set V)
    (root : {v : V // v ∉ R}) :
    root.1 ∈ componentFrom A R root := by
  refine ⟨root.property, ?_⟩
  exact Relation.ReflTransGen.refl

/-- Every vertex of a component stays outside the deleted set. -/
theorem componentFrom_disjoint_cut (A : RelStructure L V)
    (R : Set V) (root : {v : V // v ∉ R}) :
    Disjoint (componentFrom A R root) R := by
  apply Set.disjoint_left.mpr
  intro x hx hxR
  exact hx.1 hxR

/-- Every edge whose start lies in the component and whose end
also survives the deletion stays entirely in that component. -/
theorem componentFrom_step (A : RelStructure L V) (R : Set V)
    (root : {v : V // v ∉ R}) {x y : V}
    (hx : x ∈ componentFrom A R root) (hy : y ∉ R)
    (hxy : GaifmanAdjacent A x y) :
    y ∈ componentFrom A R root := by
  obtain ⟨hxR, hreach⟩ := hx
  have hstep : ReachOutside A R
      (⟨x, hxR⟩ : {v : V // v ∉ R}) ⟨y, hy⟩ :=
    Relation.ReflTransGen.single hxy
  exact ⟨hy, hreach.trans hstep⟩

/-- The Gaifman neighbourhood of S, *excluding* vertices in S. -/
def gaifmanNeighborhood (A : RelStructure L V) (S : Set V) : Set V :=
  {y | y ∉ S ∧ ∃ x, x ∈ S ∧ GaifmanAdjacent A x y}

/-- First clause of Observation cuty: the entire external boundary
of a component of A minus R is contained in the removed cut. -/
theorem gaifmanNeighborhood_component_subset_cut
    (A : RelStructure L V) (R : Set V)
    (root : {v : V // v ∉ R}) :
    gaifmanNeighborhood A (componentFrom A R root) ⊆ R := by
  intro y hy
  obtain ⟨hnot, x, hx, hxy⟩ := hy
  by_contra hyR
  exact hnot (componentFrom_step A R root hx hyR hxy)

/-- The same observation stated for an arbitrary (genuine)
connected component, without exposing the chosen root. -/
theorem gaifmanNeighborhood_isComponent_subset_cut
    (A : RelStructure L V) (R C : Set V)
    (hC : IsComponentOutside A R C) :
    gaifmanNeighborhood A C ⊆ R := by
  obtain ⟨root, rfl⟩ := hC
  exact gaifmanNeighborhood_component_subset_cut A R root

/-- If cl is a monotone closure operator and R is cl-closed,
the closure of the neighbourhood still lies inside R.
The *functional* paper must instantiate cl with its actual
generated-substructure closure operator. -/
theorem closure_neighborhood_component_subset_cut
    (A : RelStructure L V) (R C : Set V)
    (cl : Set V → Set V)
    (hmono : Monotone cl) (hclosed : cl R = R)
    (hC : IsComponentOutside A R C) :
    cl (gaifmanNeighborhood A C) ⊆ R := by
  calc
    cl (gaifmanNeighborhood A C) ⊆ cl R :=
      hmono (gaifmanNeighborhood_isComponent_subset_cut A R C)
    _ = R := hclosed

end AllThoseRamseyClasses.Lifts
