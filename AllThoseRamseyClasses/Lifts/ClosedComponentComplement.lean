import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# The complementary side of a functional Gaifman piece is closed

Let R be an exact function-closed vertex set of A, and let C be one
whole connected component of the Gaifman graph of A after deleting R.
The verified foundational theorem makes R ∪ C closed. The other
side V \ C is ALSO closed, because an output y in C above inputs
outside C must be adjacent to some input outside R (if every input
were in R then R-closedness would already capture y).

Consequently R ∪ C and V \ C are full functional substructures
whose exact intersection is R. This is the geometric seam required
for the functional free-amalgam decomposition of the original source
of a piece. It handles nullary functions and set-valued outputs.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The complement of a component after removing a function-closed
set R is function-closed. This is a property of the ACTUAL function
graph, not a hypothetical extra adjacency. -/
theorem functionalComponentComplement_isClosed
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R)
    (root : {v : V // v ∉ R}) :
    A.IsClosed (Set.compl (functionalComponentFrom A R root)) := by
  intro f xs hxs y hy
  intro hyC
  have hyOutR : y ∉ R := hyC.1
  have hsome : ∃ i : Fin (L.funcArity f), xs i ∉ R := by
    by_contra hnone
    have hall : ∀ i : Fin (L.funcArity f), xs i ∈ R := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact hyOutR (hR f xs hall hy)
  obtain ⟨i, hiR⟩ := hsome
  have hnotC : xs i ∉ functionalComponentFrom A R root := hxs i
  have hneq : xs i ≠ y := by
    intro hxy
    exact hnotC (hxy.symm ▸ hyC)
  have hedge : GaifmanAdjacent A.graph (xs i) y := by
    refine ⟨hneq, (.inr f), Structure.funcTuple xs y,
      i.castSucc, Fin.last (L.funcArity f), ?_, ?_, ?_⟩
    · exact (Structure.graph_func_snoc A f xs y).mpr hy
    · simp
    · simp
  have hback : GaifmanAdjacent A.graph y (xs i) :=
    GaifmanAdjacent.symm hedge
  have hxC : xs i ∈ functionalComponentFrom A R root :=
    componentFrom_step A.graph R root hyC hiR hback
  exact hnotC hxC

/-- The closed piece and closed remainder intersect in EXACTLY R.
No closure hull or other root enlargement appears. -/
theorem functionalComponent_side_intersection
    (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R}) :
    (functionalComponentUnion A R root) ∩
        (functionalComponentFrom A R root)ᶜ = R := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨hSide, hOutside⟩
    exact hSide.resolve_right hOutside
  · intro hR
    refine ⟨Or.inl hR, ?_⟩
    intro hC
    exact hC.1 hR

/-- The complementary part is a full induced functional structure. -/
def functionalComponentComplementInduce
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure L (Set.compl (functionalComponentFrom A R root)) :=
  A.induce (Set.compl (functionalComponentFrom A R root))
    (functionalComponentComplement_isClosed A R hR root)

/-- Its inclusion in A is a full functional embedding, reflecting
relation tuples and the complete function fibres. -/
def functionalComponentComplementEmbedding
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure.Embedding
      (functionalComponentComplementInduce A R hR root) A :=
  A.inclusion (Set.compl (functionalComponentFrom A R root))
    (functionalComponentComplement_isClosed A R hR root)

end AllThoseRamseyClasses.Lifts
