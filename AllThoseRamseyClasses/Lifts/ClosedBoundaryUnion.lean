import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# Functional closure of a set together with its component boundary

The second closure assertion in Observation `cuty` of the 2019
manuscript: `Cl_A(N_A(C)) ∪ C` induces a full substructure.

Prove the stronger useful statement for any S,C: if S is closed and
contains every external Gaifman neighbor of C, then S ∪ C is closed.
No connectedness, finiteness, cut-minimality, or positive-arity
assumption is necessary. The proof uses the actual function graph
tuple from the shared relationalization API, not a fictitious
one-step edge from a generated-closure vertex.

For partial single-valued functions, empty output is interpreted
as undefined; a defined empty set-valued application is not separately
represented by this graph encoding.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The neighborhood-controlled union lemma. It works for arbitrary
set-valued output relations, including nullary functions. -/
theorem functionalClosedUnion_of_boundary
    (A : Structure L V) (S C : Set V)
    (hS : A.IsClosed S)
    (hBoundary : gaifmanNeighborhood A.graph C ⊆ S) :
    A.IsClosed (S ∪ C) := by
  intro f xs hxs y hy
  by_cases hyS : y ∈ S
  · exact Or.inl hyS
  have hsome : ∃ i : Fin (L.funcArity f), xs i ∉ S := by
    by_contra hnone
    have hall : ∀ i : Fin (L.funcArity f), xs i ∈ S := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact hyS (hS f xs hall hy)
  obtain ⟨i, hiS⟩ := hsome
  have hiC : xs i ∈ C := (hxs i).resolve_left hiS
  by_cases hyC : y ∈ C
  · exact Or.inr hyC
  have hneq : xs i ≠ y := by
    intro hxy
    exact hyC (hxy ▸ hiC)
  have hedge : GaifmanAdjacent A.graph (xs i) y := by
    refine ⟨hneq, (.inr f), Structure.funcTuple xs y,
      i.castSucc, Fin.last (L.funcArity f), ?_, ?_, ?_⟩
    · exact (Structure.graph_func_snoc A f xs y).mpr hy
    · simp
    · simp
  have hyN : y ∈ gaifmanNeighborhood A.graph C :=
    ⟨hyC, xs i, hiC, hedge⟩
  exact False.elim (hyS (hBoundary hyN))

/-- The precise closure claim of Observation `cuty`:
the generated closure of the external neighborhood, together with
the original component, induces a genuine substructure. In fact,
this statement holds for EVERY vertex set C. -/
theorem functionalBoundaryClosure_union_isClosed
    (A : Structure L V) (C : Set V) :
    A.IsClosed
      (A.functionClosure (gaifmanNeighborhood A.graph C) ∪ C) := by
  apply functionalClosedUnion_of_boundary A
    (A.functionClosure (gaifmanNeighborhood A.graph C)) C
  · exact A.functionClosure_isClosed (gaifmanNeighborhood A.graph C)
  · exact A.subset_functionClosure (gaifmanNeighborhood A.graph C)

/-- The literal vertex set of the induced boundary-plus-component
structure. Naming it explicitly prevents `∪` from being interpreted
as a union of TYPES when the set is coerced to its subtype. -/
abbrev functionalBoundaryClosureVertices
    (A : Structure L V) (C : Set V) : Set V :=
  A.functionClosure (gaifmanNeighborhood A.graph C) ∪ C

/-- The induced structure on Cl(N(C)) ∪ C exists and its inclusion
is a full embedding reflecting relations and entire function value
sets, not merely a weak induced restriction. -/
def functionalBoundaryClosureInduce
    (A : Structure L V) (C : Set V) :
    Structure L (functionalBoundaryClosureVertices A C) :=
  A.induce (functionalBoundaryClosureVertices A C)
    (functionalBoundaryClosure_union_isClosed A C)

/-- The corresponding exact full embedding back into A. -/
def functionalBoundaryClosureEmbedding
    (A : Structure L V) (C : Set V) :
    Structure.Embedding (functionalBoundaryClosureInduce A C) A :=
  A.inclusion (functionalBoundaryClosureVertices A C)
    (functionalBoundaryClosure_union_isClosed A C)

end AllThoseRamseyClasses.Lifts
