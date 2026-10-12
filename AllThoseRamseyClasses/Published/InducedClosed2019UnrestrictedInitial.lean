import AllThoseRamseyClasses.Published.InducedClosed2019MainTwoConstructors
import PartiteConstruction.Ramsey.ClosureUnrestrictedRamseyPass
import PartiteConstruction.Ramsey.ClosureUnrestrictedRankOne

/-!
# Repaired 2019 Lemma 2.28: actual unrestricted initial Ramsey Picture

The newer pinned partite-construction revision constructs the previously
missing native recursive Picture over an ARBITRARY, possibly non-U-closed
Ramsey control D. Its proof uses genuinely root-tagged closure-RELATION
symbols, rather than the inconsistent printed recipe of assigning many
different tagged closure roots to the same unchanged relation symbol.

The temporary little Picture can have multiple closure outputs. It is
never assumed U-semi-closed; the inner tagged construction protects the
selected closed tests and descends to a U-closed untagged picture.

Here we prove the precise paper-faithful COORDINATED repair of 2019
Lemma 2.28, including:
 * finite U-CLOSED Ramsey witness C over the ORIGINAL control D;
 * a corrected protected homomorphism-embedding C -> D, with tests
   on exactly the original induced closed U-irreducibles;
 * membership in K of all such closed irreducible induced tests,
   using CLOSED hereditariness and copy coverage by B;
 * no relative-A-copy assumption on D and no U-closedness of D.

The original published Lemma 2.28 is still refuted if its final
coverage quantifies over all intrinsic nonclosed U-irreducible
tests. The theorem below proves its explicit coordinated correction.

This new construction DISCHARGES the initial-Picture hypothesis of
the conditional repaired 2019 Theorem 2.18. Only the genuine
higher-rank j >= 1 -> j+1 Picture step remains an external
constructor hypothesis. We DO NOT assert that higher-rank theorem.

The optional cutoff-one corollary gives a fully constructed K-Ramsey
conclusion for arbitrary nonclosed control and n <= 1, with the exact
original induced weak n-vertex local-completion premise.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

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

/-- The general coordinated 2019 Theorem 2.18 is reduced to ONE
remaining explicit constructor: the higher-rank j->j+1 native
Picture step, for every j >= 1. No other positive Picture witness
is assumed: the unrestricted initial one is built above.

This is a conditional implication, not proof that the higher-rank
constructor exists. The cutoff n(B,C0) still comes from the
paper-faithful corrected Definition 2.17 before constructing C. -/
theorem coordinated2019_ramsey_of_higher_rank_constructor
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules)
    (hHigher :
      ∀ {X Y : Type v} [Finite X] [Finite Y]
        (A : RelStructure L X) (B : RelStructure L Y)
        (κ : Type) [Fintype κ] [Nonempty κ]
        (j : ℕ), 1 ≤ j → K A → K B →
        Proposed2019RankIncrementStep K rules A B κ j) :
    FiniteRamseyClass K := by
  have hInitial :
      ∀ {X Y Z : Type v} [Finite X] [Finite Y] [Finite Z]
        (A : RelStructure L X) (B : RelStructure L Y)
        (C0 : RelStructure L Z)
        (κ : Type) [Fintype κ] [Nonempty κ],
        K A → K B → R C0 →
        StructuralRamsey.Arrow A B C0 κ →
        Has2019UnrestrictedInitialPicture K rules A B C0 κ := by
    intro X Y Z hFiniteX hFiniteY hFiniteZ A B C0 κ hFinκ hκ hKA hKB _ hArrow
    have hA : IsUClosed rules A := hK.induced.closed A hKA
    have hB : IsUClosed rules B := hK.induced.closed B hKB
    have hHer : ClosedUHereditary K rules :=
      embeddedClosedHereditary_of_induced
        hK.induced.hereditary hK.iso
    exact lemma_2_28_coordinated_unrestricted_induced
      A B C0 hA hB hKB hHer κ hArrow
  exact coordinated2019_ramsey_of_two_picture_constructors
    R K rules hR hRIrred hK hInitial hHigher

/-- A fully CONSTRUCTED corrected K-Ramsey witness at local-finiteness
cutoff n <= 1. The original Ramsey control D can be NON-U-CLOSED.
No relative-A-copy hypothesis and no A-embeds-into-B assumption. -/
theorem coordinated2019_cutoff_one_unrestricted_induced
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hBIrr : B.Irreducible) (hKB : K B)
    (hD : D.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (n : ℕ) (hn : n ≤ 1)
    (hLocal : InducedClosedULocalCompletionAt K rules B D n)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B D κ) :
    ∃ (Y : Type v) (_ : Finite Y) (Target : RelStructure L Y),
      K Target ∧ StructuralRamsey.Arrow A B Target κ := by
  exact StructuralRamsey.Partite.Induced.ramsey_of_closedLocalCompletion_cutoff_one_unrestricted
    A B D hA hB hBIrr hKB hD hHer n hn
    (InducedClosedULocalCompletionAt.toAbstractClosed hLocal)
    κ hArrow

end AllThoseRamseyClasses.Published
