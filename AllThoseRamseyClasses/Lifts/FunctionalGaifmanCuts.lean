import AllThoseRamseyClasses.Lifts.GaifmanCuts
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Closed cuts and functional Gaifman components

The functional half of Observation `cuty` in Section 3 of
Hubička--Nešetřil, *All those Ramsey classes* (2019).

We use the existing `StructuralRamsey.Structure` with set-valued
function interpretations. For the manuscript's single-valued partial
functions, an undefined value is represented by the empty set and
a defined value by a singleton. More general functions whose
*defined* output is empty require an explicit domain predicate and
are NOT claimed to be modeled by this representation.

Gaifman adjacency recognizes positive relation tuples, the input
coordinates of a function with a value, and input/output incidences.
Paths after removing R are the transitive/reflexive closure of this
adjacency on the subtype outside R.

The key theorem proves that if R is function-closed, then
R union ANY component of the graph after deleting R is closed.
This is exactly the missing functional substructure condition before
forming the paper's rooted pieces. No finiteness or minimality of R
is assumed. In particular the proof handles nullary functions:
their values already belong to every closed R.

The connectedness/minimal-separating-cut characterization and flip
lemma are independent later goals, not consequences declared here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Adjacency in the functional Gaifman graph: a positive relation
tuple, two input coordinates of a defined function application, or
an input-output incidence. Output membership is explicit and cannot
be confused with an unavailable/undefined function value. -/
def functionalGaifmanAdjacent (A : Structure L V) (x y : V) : Prop :=
  x ≠ y ∧
    ((∃ (s : L.RelSymbol) (t : Fin (L.relArity s) → V)
       (i j : Fin (L.relArity s)),
         A.rel s t ∧ t i = x ∧ t j = y) ∨
     (∃ (f : L.FuncSymbol) (t : Fin (L.funcArity f) → V)
       (z : V), z ∈ A.func f t ∧
         ((∃ (i j : Fin (L.funcArity f)),
             t i = x ∧ t j = y) ∨
          (∃ i : Fin (L.funcArity f),
            (t i = x ∧ z = y) ∨ (t i = y ∧ z = x)))))

theorem functionalGaifmanAdjacent_symm (A : Structure L V)
    {x y : V} (h : functionalGaifmanAdjacent A x y) :
    functionalGaifmanAdjacent A y x := by
  obtain ⟨hne, hrel | hfunc⟩ := h
  · obtain ⟨s, t, i, j, ht, hi, hj⟩ := hrel
    exact ⟨hne.symm, Or.inl ⟨s, t, j, i, ht, hj, hi⟩⟩
  · obtain ⟨f, t, z, hz, hpairs⟩ := hfunc
    refine ⟨hne.symm, Or.inr ⟨f, t, z, hz, ?_⟩⟩
    rcases hpairs with ⟨i, j, hi, hj⟩ | ⟨i, hinput⟩
    · exact Or.inl ⟨j, i, hj, hi⟩
    · rcases hinput with ⟨hi, hz'⟩ | ⟨hi, hz'⟩
      · exact Or.inr ⟨i, Or.inr ⟨hi, hz'⟩⟩
      · exact Or.inr ⟨i, Or.inl ⟨hi, hz'⟩⟩

/-- Restrict the functional Gaifman edges to vertices outside R. -/
def functionalOutsideAdjacency (A : Structure L V) (R : Set V) :
    {x : V // x ∉ R} → {y : V // y ∉ R} → Prop :=
  fun x y => functionalGaifmanAdjacent A x.1 y.1

/-- Paths which avoid R, including paths of length zero. -/
def functionalReachOutside (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R}) : Prop :=
  Relation.ReflTransGen (functionalOutsideAdjacency A R) x y

/-- The full connected component of the chosen surviving root. -/
def functionalComponentFrom (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) : Set V :=
  {x | ∃ hx : x ∉ R,
    functionalReachOutside A R root ⟨x, hx⟩}

theorem functionalComponentFrom_root (A : Structure L V)
    (R : Set V) (root : {v : V // v ∉ R}) :
    root.1 ∈ functionalComponentFrom A R root :=
  ⟨root.property, Relation.ReflTransGen.refl⟩

theorem functionalComponentFrom_disjoint_cut (A : Structure L V)
    (R : Set V) (root : {v : V // v ∉ R}) :
    Disjoint (functionalComponentFrom A R root) R := by
  apply Set.disjoint_left.mpr
  intro x hx hxR
  exact hx.1 hxR

/-- Adjacency of two surviving vertices cannot cross component
boundaries. This also covers Gaifman edges from function values. -/
theorem functionalComponentFrom_step (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) {x y : V}
    (hx : x ∈ functionalComponentFrom A R root)
    (hy : y ∉ R)
    (hxy : functionalGaifmanAdjacent A x y) :
    y ∈ functionalComponentFrom A R root := by
  obtain ⟨hxR, hreach⟩ := hx
  have hstep : functionalReachOutside A R
      (⟨x, hxR⟩ : {v : V // v ∉ R}) ⟨y, hy⟩ :=
    Relation.ReflTransGen.single hxy
  exact ⟨hy, hreach.trans hstep⟩

/-- The vertices adjacent to a set which are not already in it. -/
def functionalGaifmanNeighborhood (A : Structure L V)
    (S : Set V) : Set V :=
  {y | y ∉ S ∧ ∃ x, x ∈ S ∧ functionalGaifmanAdjacent A x y}

/-- The first clause of manuscript Observation `cuty`,
including the full function-induced Gaifman graph. -/
theorem functionalNeighborhood_component_subset_cut
    (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) :
    functionalGaifmanNeighborhood A
      (functionalComponentFrom A R root) ⊆ R := by
  intro y hy
  obtain ⟨hnot, x, hx, hxy⟩ := hy
  by_contra hyR
  exact hnot (functionalComponentFrom_step A R root hx hyR hxy)

/-- The union of the closed cut and one full complementary component. -/
def functionalComponentUnion (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) : Set V :=
  R ∪ functionalComponentFrom A R root

/-- The key missing functional lemma: a closed cut united with any
complementary Gaifman component is again closed.

A function output y above inputs in R ∪ C either has all inputs in R,
in which case R-closedness applies, or some input x in C. If y is
outside R and y ≠ x, their function incidence is a Gaifman edge,
so y belongs to the same C. This argument ALSO works for nullary
function symbols because the first case applies automatically. -/
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
  by_cases hEq : xs i = y
  · exact Or.inr (hEq ▸ hiC)
  have hedge : functionalGaifmanAdjacent A (xs i) y := by
    refine ⟨hEq, Or.inr ?_⟩
    exact ⟨f, xs, y, hy, Or.inr ⟨i, Or.inl ⟨rfl, rfl⟩⟩⟩
  exact Or.inr
    (functionalComponentFrom_step A R root hiC hyR hedge)

/-- The actual induced functional substructure on R ∪ C exists.
Unlike a weak restriction, all function values at included inputs
are retained and the inclusion is a full functional embedding. -/
def functionalComponentInduce
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure L (functionalComponentUnion A R root) :=
  A.induce (functionalComponentUnion A R root)
    (functionalComponentUnion_isClosed A R hR root)

/-- The canonical inclusion into A reflects relations and preserves
and reflects EVERY function value of an included input tuple. -/
def functionalComponentEmbedding
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure.Embedding (functionalComponentInduce A R hR root) A :=
  A.inclusion (functionalComponentUnion A R root)
    (functionalComponentUnion_isClosed A R hR root)


/-- The full generated function closure of the external neighborhood
is still contained in a closed cut. This is the second clause of
Observation `cuty`, without assuming a finite generating set or
unary closure. -/
theorem functionalClosure_neighborhood_subset_cut
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    A.functionClosure
      (functionalGaifmanNeighborhood A
        (functionalComponentFrom A R root)) ⊆ R := by
  intro x hx
  exact hx R hR (functionalNeighborhood_component_subset_cut A R root)

end AllThoseRamseyClasses.Lifts
