import AllThoseRamseyClasses.Lifts.FlipExclusiveSupport

/-!
# The strict finite support decrease after a successful piece flip

The crucial first minimality argument in the proof of
`lem:amalgamationstr` chooses a forbidden source minimizing the
number of vertices mapped to one exclusive side A\\X of an
ambient free amalgam.

If the original source has a vertex in its A-only support NOT in
the unchanged complementary piece, then the support of that
complement is strictly smaller than the old support. In a new
actual functional free-amalgam source, if the replacement piece
maps entirely outside A\\X and the complementary side map is
unchanged, the exact support-bijection theorem shows that the NEW
support has the same size as the unchanged complementary support.

Consequently the support of the flipped source is STRICTLY
smaller than the old support, even when the new weak map is not
injective. The later closure-under-HE-images reduction must still
supply an injectively embedded forbidden witness before applying
the manuscript's minimal-choice argument. That is not assumed here.

The proof concerns cardinalities of ACTUAL source vertices and
full source-side embeddings, not cardinalities of target image sets.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {RootCarrier OldPiece NewPiece RightCarrier
  OldCarrier NewCarrier TargetCarrier : Type v}
variable {Root : Structure L RootCarrier}
variable {OldLeft : Structure L OldPiece}
variable {NewLeft : Structure L NewPiece}
variable {Right : Structure L RightCarrier}
variable {Old : Structure L OldCarrier}
variable {New : Structure L NewCarrier}
variable {sOldL : Structure.Embedding Root OldLeft}
variable {sNewL : Structure.Embedding Root NewLeft}
variable {sRight : Structure.Embedding Root Right}
variable {iOldL : Structure.Embedding OldLeft Old}
variable {iOldR : Structure.Embedding Right Old}
variable {iNewL : Structure.Embedding NewLeft New}
variable {iNewR : Structure.Embedding Right New}

/-- An exclusive-support vertex in the old forbidden source lying
outside the unchanged right/complementary piece proves the support
of that right piece has strictly smaller CARDINALITY than the old
source support. Both maps may have arbitrary collisions. -/
theorem oldExclusiveSupport_card_lt_complement
    [Fintype OldCarrier] [Fintype RightCarrier]
    (pOld : OldCarrier → TargetCarrier)
    (pRight : RightCarrier → TargetCarrier)
    (hRight : ∀ b, pOld (iOldR b) = pRight b)
    (AOnly : Set TargetCarrier)
    (oldVertex : OldCarrier)
    (hOldA : pOld oldVertex ∈ AOnly)
    (hOutside : ∀ b : RightCarrier, oldVertex ≠ iOldR b) :
    Nat.card {b : RightCarrier // pRight b ∈ AOnly} <
      Nat.card {x : OldCarrier // pOld x ∈ AOnly} := by
  classical
  let supportMap :
      {b : RightCarrier // pRight b ∈ AOnly} →
      {x : OldCarrier // pOld x ∈ AOnly} :=
    fun b => ⟨iOldR b.1, by rw [hRight]; exact b.2⟩
  have hInjective : Function.Injective supportMap := by
    intro a b hab
    apply Subtype.ext
    apply iOldR.injective
    exact congrArg Subtype.val hab
  have hNotSurjective : ¬Function.Surjective supportMap := by
    intro hSurj
    obtain ⟨b, hb⟩ := hSurj ⟨oldVertex, hOldA⟩
    have hval : iOldR b.1 = oldVertex :=
      congrArg Subtype.val hb
    exact (hOutside b.1) hval.symm
  have hFiniteCard :
      Fintype.card {b : RightCarrier // pRight b ∈ AOnly} <
        Fintype.card {x : OldCarrier // pOld x ∈ AOnly} :=
    Fintype.card_lt_of_injective_not_surjective
      supportMap hInjective hNotSurjective
  simpa only [Nat.card_eq_fintype_card] using hFiniteCard

/-- The cardinality form of the checked exact support equivalence.
This is useful when the original and new sources have different
finite carriers, but share the same complementary side. -/
theorem flipExclusiveSupport_fintype_card_eq
    [Fintype NewCarrier] [Fintype RightCarrier]
    (hFree : Structure.IsFreeAmalgam sNewL sRight iNewL iNewR)
    (pNew : NewCarrier → TargetCarrier)
    (pRight : RightCarrier → TargetCarrier)
    (hRight : ∀ b, pNew (iNewR b) = pRight b)
    (AOnly : Set TargetCarrier)
    (hNewLeftAvoid : ∀ a : NewPiece,
      pNew (iNewL a) ∉ AOnly) :
    Nat.card {x : NewCarrier // pNew x ∈ AOnly} =
      Nat.card {b : RightCarrier // pRight b ∈ AOnly} := by
  classical
  have hFiniteCard :
      Fintype.card {x : NewCarrier // pNew x ∈ AOnly} =
        Fintype.card {b : RightCarrier // pRight b ∈ AOnly} :=
    Fintype.card_congr
      (flipExclusiveSupportEquiv
        hFree pNew pRight hRight AOnly hNewLeftAvoid).symm
  simpa only [Nat.card_eq_fintype_card] using hFiniteCard

/-- The strict support decrease underlying the first flip
contradiction in the 2019 strong-amalgamation proof.

The old witness contributes at least one A-only vertex from
outside the preserved complement; the new replacement side has
NO A-only vertices, and its actual FULL free-amalgam source
keeps the complementary map unchanged. -/
theorem flipExclusiveSupport_strict_decrease
    [Fintype OldCarrier] [Fintype NewCarrier]
    [Fintype RightCarrier]
    (hNewFree : Structure.IsFreeAmalgam
      sNewL sRight iNewL iNewR)
    (pOld : OldCarrier → TargetCarrier)
    (pNew : NewCarrier → TargetCarrier)
    (pRight : RightCarrier → TargetCarrier)
    (hOldRight : ∀ b, pOld (iOldR b) = pRight b)
    (hNewRight : ∀ b, pNew (iNewR b) = pRight b)
    (AOnly : Set TargetCarrier)
    (hNewLeftAvoid : ∀ a : NewPiece,
      pNew (iNewL a) ∉ AOnly)
    (oldVertex : OldCarrier)
    (hOldA : pOld oldVertex ∈ AOnly)
    (hOutside : ∀ b : RightCarrier, oldVertex ≠ iOldR b) :
    Nat.card {x : NewCarrier // pNew x ∈ AOnly} <
      Nat.card {x : OldCarrier // pOld x ∈ AOnly} := by
  calc
    Nat.card {x : NewCarrier // pNew x ∈ AOnly} =
        Nat.card {b : RightCarrier // pRight b ∈ AOnly} :=
      flipExclusiveSupport_fintype_card_eq
        hNewFree pNew pRight hNewRight AOnly hNewLeftAvoid
    _ < Nat.card {x : OldCarrier // pOld x ∈ AOnly} :=
      oldExclusiveSupport_card_lt_complement pOld pRight
        hOldRight AOnly oldVertex hOldA hOutside

end AllThoseRamseyClasses.Lifts
