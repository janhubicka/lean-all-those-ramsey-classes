import AllThoseRamseyClasses.Published.InducedClosed2019ClassBridge
import PartiteConstruction.Ramsey.ClosureUnrestrictedRamseyPass
import PartiteConstruction.Ramsey.ClosureUnrestrictedRankOne

/-!
# Unrestricted closed Ramsey Picture (working revised 2019 Lemma 2.28)

This module constructs an actual finite U-closed Ramsey Picture above
an arbitrary ambient control, which may be nonclosed. Protected maps
are full embeddings on exact induced tests that are simultaneously
U-closed and U-irreducible, and all such tests are covered by K.

The proposition Has2019UnrestrictedInitialPicture and its verified
constructor are retained here. The historical conditional higher-rank
deduction has been removed from this module; Git history records it.
The unrestricted relational Theorem 2.18 now follows independently
from the verified generated-profile/sparsening proof.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- Corrected 2019 Lemma 2.28 target: build an actual finite U-CLOSED
Ramsey picture above a not-necessarily-closed control C0, with a
corrected induced-test protected projection and coverage of all
closed U-irreducible induced substructures by K. This proposition is
NOT a theorem asserting the constructor exists. -/
def Has2019UnrestrictedInitialPicture
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P) (κ : Type*) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (D : RelStructure L W),
    IsUClosed rules D ∧
    (∃ f : W → P,
      IsInducedClosedUHomomorphismEmbedding rules D C0 f) ∧
    StructuralRamsey.Arrow A B D κ ∧
    CorrectedUIrreduciblesIn K rules D

/-- Actual unrestricted closed-test Ramsey construction corresponding
to the coordinated REPAIRED 2019 Lemma 2.28. The original C0 need
not be U-closed, and no copies of A need be relative U-substructures. -/
theorem lemma_2_28_coordinated_unrestricted_induced
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hKB : K B) (hHer : ClosedUHereditary K rules)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C0 κ) :
    Has2019UnrestrictedInitialPicture K rules A B C0 κ := by
  obtain ⟨Y, hY, C, hRamsey, hClosed, hPart, hCover⟩ :=
    StructuralRamsey.Partite.Induced.closed_ramsey_unrestricted
      A B C0 hA hB κ hArrow
  have hCovered : CorrectedUIrreduciblesIn K rules C.toRelStructure :=
    ClosedUIrreduciblesIn.toCorrectedInduced
      (ClosedUIrreduciblesIn.of_copy_coverage
        hHer B hKB C.toRelStructure hCover)
  exact ⟨Y, hY, C.toRelStructure, hClosed,
    ⟨C.part, IsClosedUHomomorphismEmbedding.toInducedClosed hPart⟩,
    hRamsey, hCovered⟩

end AllThoseRamseyClasses.Published
