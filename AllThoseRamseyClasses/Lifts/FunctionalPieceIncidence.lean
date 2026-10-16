import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# Localization of relation and function incidences at a Gaifman cut

A positive relation tuple cannot mix a complementary component C
with vertices outside R ∪ C. Every two distinct coordinates of a
positive tuple are adjacent, so a tuple touching C must lie wholly
in R ∪ C. Applied to `Structure.graph`, this automatically
localizes *all* function inputs and their actual output to one side.

This is the no-crossing ingredient for the full functional
free-amalgam decomposition used by the piece/flip construction.
It also covers empty tuples, repeated coordinates and nullary
functions without arbitrary positive-arity assumptions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Every positive tuple of A lies wholly in the rooted component
side R ∪ C or wholly outside C. This is a RELATIONAL theorem
applicable to the graph encoding of function incidences. -/
theorem gaifmanTuple_side_localization
    (A : RelStructure L V) (R : Set V)
    (root : {v : V // v ∉ R})
    (s : L.Symbol) (t : Fin (L.arity s) → V)
    (ht : A.rel s t) :
    (∀ i, t i ∈ R ∪ componentFrom A R root) ∨
      (∀ i, t i ∈ Set.compl (componentFrom A R root)) := by
  classical
  by_cases hSome : ∃ i, t i ∈ componentFrom A R root
  · obtain ⟨i, hi⟩ := hSome
    left
    intro j
    by_cases hjR : t j ∈ R
    · exact Or.inl hjR
    · right
      by_cases heq : t i = t j
      · rw [← heq]
        exact hi
      · exact componentFrom_step A R root hi hjR
          ⟨heq, s, t, i, j, ht, rfl, rfl⟩
  · right
    intro i hi
    exact hSome ⟨i, hi⟩

end AllThoseRamseyClasses.Lifts

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Actual output incidences, including all function inputs and
the output, are entirely in the piece side or entirely in the
complement. This does not assert that undefined function
applications have an output. -/
theorem functionalIncidence_side_localization
    (A : Structure L V) (R : Set V)
    (root : {v : V // v ∉ R})
    (f : L.FuncSymbol) (xs : Fin (L.funcArity f) → V)
    (y : V) (hy : y ∈ A.func f xs) :
    ((∀ i, xs i ∈ functionalComponentUnion A R root) ∧
      y ∈ functionalComponentUnion A R root) ∨
    ((∀ i, xs i ∈
        Set.compl (functionalComponentFrom A R root)) ∧
      y ∈ Set.compl (functionalComponentFrom A R root)) := by
  have ht := gaifmanTuple_side_localization
    A.graph R root (.inr f) (Structure.funcTuple xs y)
    ((Structure.graph_func_snoc A f xs y).mpr hy)
  rcases ht with hl | hr
  · left
    constructor
    · intro i
      exact (Structure.funcTuple_castSucc xs y i) ▸ hl i.castSucc
    · exact (Structure.funcTuple_last xs y) ▸ hl (Fin.last _)
  · right
    constructor
    · intro i
      exact (Structure.funcTuple_castSucc xs y i) ▸ hr i.castSucc
    · exact (Structure.funcTuple_last xs y) ▸ hr (Fin.last _)

end AllThoseRamseyClasses.Lifts
