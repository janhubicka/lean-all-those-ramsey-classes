import AllThoseRamseyClasses.Published.FunctionalWithParts2019IrreducibleHostObstruction
import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKRamseyDescent
import Mathlib.Data.Fintype.EquivFin

/-!
# Appendix Track B: unordered native full-embedding Ramsey is obstructed by symmetry

The earlier verified finite two-isolated-vertex regression shows that the
canonical full-mask / full-root tagged class of an unrestricted native
free-amalgamation class need not be ordinary irreducible.

There is an independent *Ramsey conclusion* obstruction, even before
considering the corrected 2019 relative-local-completion axiom:
the unordered empty-language two-vertex structure has a nontrivial
full part-preserving automorphism.

For EVERY finite native partite target C with one part, colour a full
embedding of the two-point object by the order of its two image
vertices in an arbitrarily chosen finite enumeration of C.
Composing with the transposition of the two source vertices changes
the colour. Therefore no full embedding of B=A can be monochromatic.

The verified conditional 2019 theorem remains correct as an implication.
This regression demonstrates why an attempted unconditional theorem in
the *unordered full-embedding* native language would be false. An
ordered/rigid expansion may support an appropriate Ramsey theorem,
but forgetting its order does not yield this unordered arrow.

No weak substructure is made full. All colours are on actual FULL
native part-preserving embeddings; parts, carrier and function
fibre semantics remain unchanged.
-/

namespace AllThoseRamseyClasses.Published.TrackBNonrigidEmbeddingObstruction

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open AllThoseRamseyClasses.Published.TrackBIrreducibleHostObstruction

/-- The transposition is a real full part-preserving automorphism of
the two isolated vertices in the original native empty language. -/
def swapEmbedding :
    FunctionalPartite.Embedding twoIsolatedNative twoIsolatedNative where
  toEmbedding := {
    toFun := fun i => if i = (0 : Fin 2) then (1 : Fin 2) else (0 : Fin 2)
    injective := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    map_rel_iff := by
      intro R
      exact Empty.elim R
    map_func := by
      intro F
      exact Empty.elim F
  }
  map_part := by intro _; rfl

@[simp] theorem swapEmbedding_zero :
    swapEmbedding (0 : Fin 2) = 1 := by decide

@[simp] theorem swapEmbedding_one :
    swapEmbedding (1 : Fin 2) = 0 := by decide

/-- No finite native partite system in the empty language can satisfy
the **full embedding** two-colour Ramsey arrow
C → (B=A)^(A)_2 for the unordered two-vertex object.

The colouring is constructed for the exact proposed target C, using
a finite enumeration; it assigns different colours to f∘id and
f∘swap for every full part-preserving f:B→C. -/
theorem twoIsolated_no_fullEmbedding_RamseyArrow
    {X : Type} [Finite X]
    (C : FunctionalPartite.System emptyLanguage PUnit.{1} X) :
    ¬ FunctionalPartite.Arrow
        twoIsolatedNative twoIsolatedNative C (Fin 2) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let rank : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let χ : FunctionalPartite.Embedding twoIsolatedNative C → Fin 2 :=
    fun e =>
      if rank (e (0 : Fin 2)) < rank (e (1 : Fin 2)) then 0 else 1
  intro hArrow
  obtain ⟨f, hf⟩ := hArrow χ
  have hColour :=
    hf (FunctionalPartite.Embedding.id twoIsolatedNative) swapEmbedding
  have hEq :
      (if rank (f (0 : Fin 2)) < rank (f (1 : Fin 2))
        then (0 : Fin 2) else 1) =
      (if rank (f (1 : Fin 2)) < rank (f (0 : Fin 2))
        then (0 : Fin 2) else 1) := by
    simpa [χ, FunctionalPartite.Embedding.comp_apply,
      FunctionalPartite.Embedding.id, Structure.Embedding.id] using hColour
  have hDifferent : rank (f (0 : Fin 2)) ≠ rank (f (1 : Fin 2)) := by
    intro h
    have heq : f (0 : Fin 2) = f (1 : Fin 2) := rank.injective h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (f.toEmbedding.injective heq)
  rcases lt_trichotomy (rank (f (0 : Fin 2)))
      (rank (f (1 : Fin 2))) with hlt | heq | hgt
  · have hnlt : ¬ rank (f (1 : Fin 2)) < rank (f (0 : Fin 2)) :=
      not_lt.mpr (le_of_lt hlt)
    simp [hlt, hnlt] at hEq
  · exact hDifferent heq
  · have hnlt : ¬ rank (f (0 : Fin 2)) < rank (f (1 : Fin 2)) :=
      not_lt.mpr (le_of_lt hgt)
    simp [hnlt, hgt] at hEq

/-- The class of **all** native empty-language structures is a genuine
native free-amalgamation class (proved in the independent regression),
but its full-embedding partite Ramsey property is FALSE.

Thus there cannot be an unconditional native full-embedding
Ramsey theorem for ALL arbitrary native free-amalgamation classes,
without a rigid expansion or a different Ramsey-arrow convention. -/
theorem allNativeClass_not_fullEmbedding_partiteRamsey :
    ¬ NativeKFinitePartiteRamsey2019
        (Parts := PUnit.{1}) allNativeClass := by
  intro hRamsey
  obtain ⟨W, hW, C, _hC, hArrow⟩ :=
    hRamsey twoIsolatedNative twoIsolatedNative
      (show allNativeClass twoIsolatedNative.toStructure from trivial)
      (show allNativeClass twoIsolatedNative.toStructure from trivial)
      (Fin 2)
  letI : Finite W := hW
  exact twoIsolated_no_fullEmbedding_RamseyArrow C hArrow

end AllThoseRamseyClasses.Published.TrackBNonrigidEmbeddingObstruction
