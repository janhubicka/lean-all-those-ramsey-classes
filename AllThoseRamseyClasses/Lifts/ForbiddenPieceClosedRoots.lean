import AllThoseRamseyClasses.Lifts.ClosedFunctionalRoots
import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoEmbedding

/-!
# Every selected finite forbidden piece has a CLOSED ordered root

The forbidden geometric piece family is defined UP TO a full
root-preserving isomorphism, not just by an explicit minimal separator
in the same vertex carrier. Root-closedness is preserved by that
isomorphism because its native functional embedding is full and
surjective.

Thus every indexed piece has a genuine induced functional root
structure on Fin n, with a full root embedding. This removes the
need to assume root closedness separately when selecting an
arbitrary representative of a forbidden piece class.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}

/-- Every actual width-n forbidden geometric piece (including any
root-preserving isomorphic representative) has a closed root. -/
theorem forbiddenGeometricFunctionalPiece_rootClosed
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootedPattern.{u,v} L n)
    (hP : P ∈ forbiddenGeometricFunctionalPieces F n) :
    P.IsRootClosed := by
  change IsForbiddenGeometricFunctionalPiece F P at hP
  obtain ⟨W, A, _hFinite, _hF, d, ⟨e⟩⟩ := hP
  let G := geometricFunctionalRootedPattern A d
  have hG : G.IsRootClosed :=
    geometricFunctionalRootedPattern_rootClosed A n d
  have hPre : P.str.IsClosed
      {x | e.toFullEmbedding x ∈ Set.range G.root} :=
    e.toFullEmbedding.preimage_isClosed (Set.range G.root) hG
  have hRootSets :
      {x : P.Carrier | e.toFullEmbedding x ∈ Set.range G.root} =
        Set.range P.root := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      have hEq : e.toFullEmbedding x =
          e.toFullEmbedding (P.root i) :=
        hi.symm.trans (e.toFullEmbedding_root i).symm
      exact ⟨i, (e.toFullEmbedding.injective hEq).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (e.toFullEmbedding_root i).symm⟩
  rw [hRootSets] at hPre
  exact hPre

/-- The standard-carrier full functional root structure
belonging to a selected forbidden piece. -/
def forbiddenFunctionalPieceRootStructure
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootedPattern.{u,v} L n)
    (hP : P ∈ forbiddenGeometricFunctionalPieces F n) :
    Structure L (Fin n) :=
  P.rootStructure (forbiddenGeometricFunctionalPiece_rootClosed F P hP)

/-- The ordered tuple of any selected forbidden piece is literally
a FULL functional embedding of its induced Fin n root. -/
def forbiddenFunctionalPieceRootEmbedding
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootedPattern.{u,v} L n)
    (hP : P ∈ forbiddenGeometricFunctionalPieces F n) :
    Structure.Embedding
      (forbiddenFunctionalPieceRootStructure F P hP) P.str :=
  P.rootInclusion (forbiddenGeometricFunctionalPiece_rootClosed F P hP)

end AllThoseRamseyClasses.Lifts
