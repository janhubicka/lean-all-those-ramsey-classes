import AllThoseRamseyClasses.Published.InducedClosed2019RankPreservation
import AllThoseRamseyClasses.Published.InducedClosed2019Lemma231Iteration
import PartiteConstruction.Ramsey.ClosureRelativeControlRamsey

/-!
# The genuine native 2019 Picture preserves EVERY previously completed rank

The general 2019 Lemma 2.30 requires two separate properties:
(1) applying an actual Ramsey/partite Picture construction does NOT
destroy the rank-j completion invariant that was already known;
(2) the new Picture additionally raises that rank to j+1.

This file proves (1), for ARBITRARY finite j. It uses the real
native disjoint-copy initial picture and the complete finite
Hales--Jewett profile pass from pinned partite-construction,
not an assumed Picture constructor.

All 2019 invariants survive:
* the refined picture is finite, U-closed, and Ramsey for A,B;
* its projection into the original U-closed control is a corrected
  induced-closed protected U-homomorphism-embedding;
* every closed U-irreducible induced test belongs to K;
* EVERY closed induced test of U-size<=j retains its amended K,U-
  completion, via the now verified bounded-rank projection theorem.

The trivial branch A does not embed into B is included as in the
published 2019 argument. No C0 irreducibility, local-completion cutoff
or assumption on arbitrary nonclosed weak-image rank is added.

The desired STRICT rank promotion from j to j+1 remains open,
especially its native multi-line boundary case. This theorem is NOT
the full Lemma 2.30 or the repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- For any j, the actual protected finite Ramsey Picture construction
over a U-closed control preserves all rank-<=j K-completions.

This is the verified PRESERVATION half, not the unproved rank-INCREMENT
half, of the corrected published Lemma 2.30. -/
theorem native_picture_preserves_closed_rank_2019
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hKB : K B) (hBIrred : B.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (hC0 : IsUClosed rules C0)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C0 κ)
    (j : ℕ)
    (hRank0 :
      ∀ (T : Set P) [Fintype T],
        IsUClosed rules (C0.induce T) →
        USize rules (C0.induce T) ≤ j →
        HasInducedClosedUKCompletion K rules (C0.induce T)) :
    Has2019RankedPictureWitness K rules A B C0 κ j := by
  classical
  by_cases hAB : Nonempty (Embedding A B)
  · obtain ⟨Y, hY, D, hDRamsey, hDClosed, hDPart, hCoverage⟩ :=
      StructuralRamsey.Partite.Induced.closed_ramsey_of_closed_control
        A B C0 hA hB hC0 (Classical.choice hAB) κ hArrow
    letI : Finite Y := hY
    have hMember : CorrectedUIrreduciblesIn K rules D.toRelStructure :=
      ClosedUIrreduciblesIn.toCorrectedInduced
        (ClosedUIrreduciblesIn.of_copy_coverage
          hHer B hKB D.toRelStructure hCoverage)
    refine ⟨Y, hY, D.toRelStructure, hDClosed,
      ⟨D.part, IsClosedUHomomorphismEmbedding.toInducedClosed hDPart⟩,
      hDRamsey, hMember, ?_⟩
    intro S hFiniteS hClosedS hSizeS
    letI : Fintype S := hFiniteS
    have hPartOnS : IsInducedClosedUHomomorphismEmbedding
        rules (D.toRelStructure.induce S) C0
          (D.part ∘ Subtype.val) :=
      IsClosedUHomomorphismEmbedding.toInducedClosed
        (hDPart.precomp_embedding (inclusion D.toRelStructure S))
    exact inducedClosed2019_completion_of_bounded_rank_projection
      hC0 hPartOnS j hRank0 hSizeS
  · letI : IsEmpty (Embedding A B) :=
      ⟨fun e => hAB ⟨e⟩⟩
    obtain ⟨beta⟩ :=
      StructuralRamsey.Partite.Induced.nonempty_embedding_of_arrow
        A B C0 κ hArrow
    have hTrivial : StructuralRamsey.Arrow A B B κ :=
      StructuralRamsey.arrow_of_isEmpty
    have hMember : CorrectedUIrreduciblesIn K rules B := by
      intro S hClosedS _
      exact hHer (B.induce S) B hKB hClosedS (inclusion B S)
    refine ⟨VB, inferInstance, B, hB,
      ⟨beta, IsClosedUHomomorphismEmbedding.toInducedClosed
        (beta.isClosedUHomomorphismEmbedding rules)⟩,
      hTrivial, hMember, ?_⟩
    intro S hFiniteS _ _
    letI : Fintype S := hFiniteS
    have hCompletion : HasClosedUKCompletion K rules (B.induce S) :=
      ⟨VB, inferInstance, B, hKB, hBIrred, inclusion B S,
        (inclusion B S).isClosedUHomomorphismEmbedding rules⟩
    exact HasClosedUKCompletion.toInducedClosed hCompletion

end AllThoseRamseyClasses.Published
