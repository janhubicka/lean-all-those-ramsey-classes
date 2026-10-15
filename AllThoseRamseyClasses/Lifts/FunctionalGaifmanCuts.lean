import AllThoseRamseyClasses.Lifts.GaifmanCuts
import PartiteConstruction.Structure.Relationalize
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Functional Gaifman cuts via the validated relation-graph encoding

The function graph encoding `Structure.graph` gives an output a
positive relation tuple containing all inputs and that output.
Consequently we reuse the existing Gaifman adjacency, path and
component proofs on `A.graph`, without maintaining a second graph
theory. This is Observation `cuty` of the 2019 manuscript.

For single-valued partial functions, singleton outputs represent
defined values and empty output sets represent undefined values.
Separately-defined empty outputs require an explicit domain symbol.
No assumption of positive function arities is made.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Functional adjacency is the Gaifman adjacency of the already
validated relational graph encoding, including input/output edges. -/
abbrev functionalGaifmanAdjacent (A : Structure L V) (x y : V) : Prop :=
  GaifmanAdjacent A.graph x y

theorem functionalGaifmanAdjacent_symm (A : Structure L V)
    {x y : V} (h : functionalGaifmanAdjacent A x y) :
    functionalGaifmanAdjacent A y x :=
  GaifmanAdjacent.symm h

abbrev functionalOutsideAdjacency (A : Structure L V) (R : Set V) :=
  outsideAdjacency A.graph R

abbrev functionalReachOutside (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R}) : Prop :=
  ReachOutside A.graph R x y

abbrev functionalComponentFrom (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) : Set V :=
  componentFrom A.graph R root

theorem functionalComponentFrom_root (A : Structure L V)
    (R : Set V) (root : {v : V // v ∉ R}) :
    root.1 ∈ functionalComponentFrom A R root :=
  componentFrom_root A.graph R root

theorem functionalComponentFrom_disjoint_cut (A : Structure L V)
    (R : Set V) (root : {v : V // v ∉ R}) :
    Disjoint (functionalComponentFrom A R root) R :=
  componentFrom_disjoint_cut A.graph R root

theorem functionalComponentFrom_step (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) {x y : V}
    (hx : x ∈ functionalComponentFrom A R root)
    (hy : y ∉ R)
    (hxy : functionalGaifmanAdjacent A x y) :
    y ∈ functionalComponentFrom A R root :=
  componentFrom_step A.graph R root hx hy hxy

abbrev functionalGaifmanNeighborhood (A : Structure L V)
    (S : Set V) : Set V :=
  gaifmanNeighborhood A.graph S

/-- First assertion of Observation `cuty`: component boundaries
are contained in the cut. -/
theorem functionalNeighborhood_component_subset_cut
    (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) :
    functionalGaifmanNeighborhood A
      (functionalComponentFrom A R root) ⊆ R :=
  gaifmanNeighborhood_component_subset_cut A.graph R root

/-- The generated closure of the component's boundary is still inside
the cut, provided that the cut is function-closed. -/
theorem functionalClosure_neighborhood_subset_cut
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    A.functionClosure
      (functionalGaifmanNeighborhood A
        (functionalComponentFrom A R root)) ⊆ R := by
  intro x hx
  exact hx R hR (functionalNeighborhood_component_subset_cut A R root)

abbrev functionalComponentUnion (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) : Set V :=
  R ∪ functionalComponentFrom A R root

/-- A closed cut united with a whole complementary component is
function-closed. If all inputs of a function are in R then its outputs
are in R, including nullary functions. Otherwise some input lies in
the component, and the graph tuple supplies an edge to any output. -/
theorem functionalComponentUnion_isClosed
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    A.IsClosed (functionalComponentUnion A R root) := by
  intro f xs hxs y hy
  by_cases hyR : y ∈ R
  · exact Or.inl hyR
  have hsome : ∃ i : Fin (L.funcArity f), xs i ∉ R := by
    by_contra hnone
    have hall : ∀ i : Fin (L.funcArity f), xs i ∈ R := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact hyR (hR f xs hall hy)
  obtain ⟨i, hiR⟩ := hsome
  have hiC : xs i ∈ functionalComponentFrom A R root :=
    (hxs i).resolve_left hiR
  by_cases heq : xs i = y
  · exact Or.inr (heq ▸ hiC)
  have hedge : GaifmanAdjacent A.graph (xs i) y := by
    refine ⟨heq, (.inr f), Structure.funcTuple xs y,
      i.castSucc, Fin.last (L.funcArity f), ?_, ?_, ?_⟩
    · exact (Structure.graph_func_snoc A f xs y).mpr hy
    · simp
    · simp
  exact Or.inr (componentFrom_step A.graph R root hiC hyR hedge)

/-- A genuine induced functional substructure on the closed
component union, retaining whole function value sets. -/
def functionalComponentInduce
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure L (functionalComponentUnion A R root) :=
  A.induce (functionalComponentUnion A R root)
    (functionalComponentUnion_isClosed A R hR root)

/-- The canonical full functional embedding of the induced piece. -/
def functionalComponentEmbedding
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure.Embedding (functionalComponentInduce A R hR root) A :=
  A.inclusion (functionalComponentUnion A R root)
    (functionalComponentUnion_isClosed A R hR root)

end AllThoseRamseyClasses.Lifts
