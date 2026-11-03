import PartiteConstruction.Functional.DirectWeakIteration
import PartiteConstruction.Structure.Order

/-!
# Track E: all fully ordered function structures are irreducible

Adding a distinguished strict total order to an arbitrary
relation/set-valued-function structure makes the FULL ordered
structure irreducible, regardless of native irreducibility.

The proof is deliberately short: its RELATIONAL FUNCTION-GRAPH
encoding is irreducible, since every two distinct vertices
occur together in a positive order tuple (in one direction).
The separately verified full-functional graph-to-native
irreducibility lemma then gives the required *genuine
functional free-amalgamation* irreducibility, not a
false conversion of weak function-graph embeddings into
full functional embeddings.

This establishes the source Base irreducibility needed by
strict ordered Bbar-tree completion. It does NOT establish
ordered strong amalgamation of the maximal-trace class
or the remaining mixed weak-test rank increment.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For every native functional signature (including nullary,
partial and multivalued functions) and every genuine total
external linear order, the FULL ordered expansion is irreducible
for the full-functional free-amalgamation predicate.

Only the added order tuples are used: the original function
fibres remain untouched. -/
theorem functionalWithLinearOrder_irreducible
    {V : Type} [LinearOrder V] (B : Structure L V) :
    B.withLinearOrder.Irreducible := by
  have hGraph : B.withLinearOrder.graph.Irreducible := by
    intro x y hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨(.inl (.inr ())),
        ![x, y], (0 : Fin 2), (1 : Fin 2),
        ?_, ?_, ?_⟩
      · exact hlt
      · simp
      · simp
    · refine ⟨(.inl (.inr ())),
        ![y, x], (1 : Fin 2), (0 : Fin 2),
        ?_, ?_, ?_⟩
      · exact hgt
      · simp
      · simp
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  exact (irreducible_of_graph_irreducible
    B.withLinearOrder hGraph) hFree e

end AllThoseRamseyClasses.Lifts
