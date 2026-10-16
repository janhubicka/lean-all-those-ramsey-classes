import AllThoseRamseyClasses.Lifts.FoldedGlobalCanonicalRelations

/-!
# Exact comparison of original and folded global piece predicates

The alternative folded canonical lift uses the same genuine globally
indexed forbidden-piece class symbols as the 2019 canonical lift.
Its relations AGREE EXACTLY on injective ordered root tuples.

For repeated coordinates, the folded relation may additionally
hold, while the printed canonical relation is definitionally false.
Thus the auxiliary lift changes only the repeated-coordinate
interpretations, not the original full functional shadow or the
piece-class index.

As in the original canonical lift, every positive folded piece
relation is preserved by a full embedding of old-language
functional structures. This is only forward preservation:
the target may have further witnesses, so reflection is NOT
asserted for arbitrary embeddings.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The folded and original canonical global relations differ
EXACTLY by the source-root IMAGE injectivity conjunct.
No other witness selection, root structure, or symbol indexing
is changed by the folded-root auxiliary construction. -/
theorem globalCanonicalRelation_iff_injective_and_folded
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → W) :
    (globalFunctionalCanonicalLift F A).rel (.inr s) xs ↔
      Function.Injective xs ∧
      (foldedGlobalCanonicalLift F A).rel (.inr s) xs := by
  rw [globalFunctionalCanonicalRelation_iff]
  rfl

/-- The original and folded predicates agree on each injective
root tuple. No arbitrary weak root map is promoted to an embedding. -/
theorem globalCanonicalRelation_iff_folded_of_injective
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → W)
    (hInj : Function.Injective xs) :
    (globalFunctionalCanonicalLift F A).rel (.inr s) xs ↔
      (foldedGlobalCanonicalLift F A).rel (.inr s) xs := by
  rw [globalCanonicalRelation_iff_injective_and_folded]
  simp only [hInj, true_and]

/-- A full embedding of old relation/function structures preserves
every positive auxiliary folded piece predicate, even when the
root-image tuple has collisions. Target reflection is not implied. -/
theorem foldedGlobalCanonicalRelation_map_embedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W Z : Type} {A : Structure L W} {B : Structure L Z}
    (e : Structure.Embedding A B)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → W)
    (h : (foldedGlobalCanonicalLift F A).rel (.inr s) xs) :
    (foldedGlobalCanonicalLift F B).rel (.inr s) (e ∘ xs) := by
  change foldedGlobalCanonicalExtra F A s xs at h
  obtain ⟨P, hClass, hReal⟩ := h
  change foldedGlobalCanonicalExtra F B s (e ∘ xs)
  exact ⟨P, hClass,
    FunctionalRootRealization.map_embedding
      P.1.pattern xs e hReal⟩

end AllThoseRamseyClasses.Lifts
