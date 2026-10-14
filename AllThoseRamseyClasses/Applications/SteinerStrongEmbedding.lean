import AllThoseRamseyClasses.Applications.SteinerTripleClass

/-!
# Full relational embeddings are strong Steiner embeddings

The covered-pair marker is reflected by a full embedding. Hence no
block can meet its image in a covered-but-uncompleted pair. In fact,
whenever a block of the target meets the image in two vertices, its
third vertex is in the image. This is the strongly induced subsystem
property and would be false for plain induced hypergraph embeddings.

This module is independent of the as-yet-unproved Ramsey application.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure

theorem edge_embedding_iff {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) (R : Symbol) (x y : U) :
    edge B R (e x) (e y) ↔ edge A R x y := by
  have ht : e ∘ ![x, y] = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  change B.rel R ![e x, e y] ↔ A.rel R ![x, y]
  rw [← ht]
  exact e.map_rel_iff R ![x, y]

theorem triple_embedding_iff {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) (x y z : U) :
    triple B (e x) (e y) (e z) ↔ triple A x y z := by
  have ht : e ∘ ![x, y, z] = ![e x, e y, e z] := by
    funext i
    fin_cases i <;> rfl
  change B.rel .block ![e x, e y, e z] ↔ A.rel .block ![x, y, z]
  rw [← ht]
  exact e.map_rel_iff .block ![x, y, z]

/-- Reflection of the domain predicate forbids any exterior block
over an increasing pair declared uncovered in the source. -/
theorem embedding_no_exterior_block_of_uncovered {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B)
    (hB : IsOrderedPartialSteinerTriple B)
    {x y : U} (hUncovered : ¬ edge A .covered x y)
    (z : V) :
    ¬ triple B (e x) (e y) z := by
  intro hz
  exact hUncovered ((edge_embedding_iff e .covered x y).mp
    (hB.block_valid _ _ _ hz))

/-- Strong inducedness, in its decisive geometric form. If a target
block contains two old vertices, its UNIQUE third vertex is old too.
This uses both ordinary full reflection and the unique block rule. -/
theorem embedding_block_third_vertex_in_range {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B)
    (hA : IsOrderedPartialSteinerTriple A)
    (hB : IsOrderedPartialSteinerTriple B)
    (x y : U) (z : V) (hz : triple B (e x) (e y) z) :
    ∃ w : U, z = e w ∧ triple A x y w := by
  have hMarked : edge A .covered x y :=
    (edge_embedding_iff e .covered x y).mp
      (hB.block_valid _ _ _ hz)
  obtain ⟨w, hw⟩ := hA.covered_has_block x y hMarked
  have hMapped : triple B (e x) (e y) (e w) :=
    (triple_embedding_iff e x y w).mpr hw
  have hEq : z = e w := hB.block_unique _ _ _ _ hz hMapped
  exact ⟨w, hEq, hw⟩

end AllThoseRamseyClasses.Applications.SteinerTriples
