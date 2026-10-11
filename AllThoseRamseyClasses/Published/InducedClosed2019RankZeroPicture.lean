import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureRelativeControlRamsey
import PartiteConstruction.Ramsey.ClosureRankOneBase

/-!
# Published Lemma 2.30: the genuine j=0 construction

The 2019 Lemma 2.30 starts with a finite U-CLOSED Ramsey control C0
and repeatedly increases the controlled U-size from j to j+1.
The general higher-rank step remains open. This file constructs the
ENTIRE positive base case j=0, not merely its conditional endgame:

* C is finite and U-closed;
* C -> (B)^A_kappa holds;
* C has a protected U-homomorphism-embedding to the ORIGINAL C0
  in the proposed corrected 2019 induced-test convention;
* every closed U-irreducible induced test in C belongs to K;
* every closed induced test of U-size at most ONE has an amended
  K,U-completion.

No C0 irreducibility, local-completion cutoff, strong-amalgamation
hypothesis, or globally relative A-copy assumption is needed.
These extra properties in the rank-one Ramsey theorem from PR #98
are NOT used as surrogates for the published j=0 construction.

The proof uses the native disjoint-copy initial picture, full finite
partite Hales--Jewett passes and rank-one protected coverage in the
PINNED partite-construction library. If A does not embed into B, the
trivial arrow for C=B is handled separately (as the published paper
does for degenerate Ramsey cases).

This is a proved restricted Lemma 2.30 target, NOT the unproved
j -> j+1 induction, Lemma 2.31 iteration or general Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Exact corrected conclusion of the published Lemma 2.30
for j=0, retaining the original induced-test terminology and
the original weak carrier whenever a completion is discussed. -/
def Has2019RankZeroPictureWitness
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P) (κ : Type*) : Prop :=
  ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
    IsUClosed rules C ∧
    (∃ f : Z → P,
      IsInducedClosedUHomomorphismEmbedding rules C C0 f) ∧
    StructuralRamsey.Arrow A B C κ ∧
    CorrectedUIrreduciblesIn K rules C ∧
    (∀ (S : Set Z) [Fintype S],
      IsUClosed rules (C.induce S) →
      USize rules (C.induce S) ≤ 1 →
      HasInducedClosedUKCompletion K rules (C.induce S))

/-- The ACTUAL native partite construction proves the full j=0
corrected Lemma 2.30 witness over ANY U-closed control C0.

All colours are allowed via a finite nonempty colour type. The
proof makes no assumption that the target K has the Ramsey property
or satisfies a local-completion axiom. -/
theorem lemma_2_30_coordinated_rank_zero
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
    (hArrow : StructuralRamsey.Arrow A B C0 κ) :
    Has2019RankZeroPictureWitness K rules A B C0 κ := by
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
    intro S hFiniteS hClosedS hRankS
    exact HasClosedUKCompletion.toInducedClosed
      (closed_rank_one_completions_of_protected_coverage
        hKB hBIrred hCoverage S hClosedS hRankS)
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
    have hComplete : HasClosedUKCompletion K rules (B.induce S) :=
      ⟨VB, inferInstance, B, hKB, hBIrred, inclusion B S,
        (inclusion B S).isClosedUHomomorphismEmbedding rules⟩
    exact HasClosedUKCompletion.toInducedClosed hComplete

end AllThoseRamseyClasses.Published
