import AllThoseRamseyClasses.Published.InducedClosed2019RankZeroPicture
import AllThoseRamseyClasses.Published.InducedClosed2019WeakRankBridge
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization

/-!
# 2019 Lemmas 2.30--2.31: faithful finite induction, missing rank step exposed

The published Lemma 2.30 increases the U-size controlled by the
partite Picture construction from j to j+1. Its base j=0 is now a
constructed, axiom-audited theorem (InducedClosed2019RankZeroPicture).

This file formalizes the FINITE ITERATION and the exact weak-test
endpoint of Lemma 2.31, CONDITIONAL on one explicitly named missing
higher-rank Picture step. That step must build an actual finite
closed Ramsey picture with protected projection, closed irreducible
K-membership and completions of all closed rank-(j+1) induced tests.
The step remains an explicit PROP argument, NOT an axiom, admitted
theorem, or declaration of the completed 2019 Lemma 2.30.

Every stage may have a different finite vertex carrier. The proof
composes the genuine corrected 2019 maps through the verified
induced/abstract closed-test equivalence. The original control C0
need not be irreducible; its U-closedness is sufficient for this
part of the 2019 argument.

Finally, the rank-n witness is converted to amended (K,U)-completions
of EVERY original exact weak induced set of at most n vertices by
the separately audited WeakRankBridge. No tested weak set is replaced
by its generated closure.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- A corrected 2019 Picture at an arbitrary closed generating rank.
The projection to D and the Ramsey arrow are both part of the data. -/
def Has2019RankedPictureWitness
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (κ : Type*) (j : ℕ) : Prop :=
  ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
    IsUClosed rules C ∧
    (∃ f : Z → P,
      IsInducedClosedUHomomorphismEmbedding rules C D f) ∧
    StructuralRamsey.Arrow A B C κ ∧
    CorrectedUIrreduciblesIn K rules C ∧
    (∀ (S : Set Z) [Fintype S],
      IsUClosed rules (C.induce S) →
      USize rules (C.induce S) ≤ j →
      HasInducedClosedUKCompletion K rules (C.induce S))

/-- The precise MISSING j->j+1 Picture constructor, named as a
proposition. It only takes a previous finite U-closed Ramsey picture
with its already proved rank-j completions and K-test coverage.
The new picture must be constructed; no premise secretly asserts
existence of the final Ramsey theorem. -/
def Proposed2019RankIncrementStep
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (κ : Type*) (j : ℕ) : Prop :=
  ∀ {W : Type v} [Finite W] (D : RelStructure L W),
    IsUClosed rules D →
    StructuralRamsey.Arrow A B D κ →
    CorrectedUIrreduciblesIn K rules D →
    (∀ (S : Set W) [Fintype S],
      IsUClosed rules (D.induce S) →
      USize rules (D.induce S) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce S)) →
    Has2019RankedPictureWitness K rules A B D κ (j+1)

/-- The constructed j=0 case already proves the entire rank-zero
increment contract; higher increments remain open. -/
theorem rank_zero_picture_gives_step_zero
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L UA) (B : RelStructure L VB)
    [Finite UA] [Finite VB]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hKB : K B) (hBIrred : B.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    Proposed2019RankIncrementStep K rules A B κ 0 := by
  intro W hW D hD hArrow _ _
  exact lemma_2_30_coordinated_rank_zero A B D
    hA hB hKB hBIrred hHer hD κ hArrow

/-- Exact composition of two corrected 2019 protected projections.
The proof relies on the established map equivalence rather than
assuming the paper's induced map predicate has library composition
by definitional coincidence. -/
theorem inducedClosedMap_comp_2019
    {rules : ClosureDescription L}
    {X Y Z : Type v}
    {A : RelStructure L X} {B : RelStructure L Y}
    {C : RelStructure L Z}
    {f : X → Y} {g : Y → Z}
    (hg : IsInducedClosedUHomomorphismEmbedding rules B C g)
    (hf : IsInducedClosedUHomomorphismEmbedding rules A B f) :
    IsInducedClosedUHomomorphismEmbedding rules A C (g ∘ f) :=
  IsClosedUHomomorphismEmbedding.toInducedClosed
    ((IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hg).comp
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf))

/-- Formal finite iteration of the 2019 Lemma 2.30 construction.
The only missing assumption is an actual rank increment for j>=1,
with all four published Picture invariants displayed in its type.

The j=0 witness is genuinely constructed, not assumed.
This theorem does NOT prove the rank-step hypothesis. -/
theorem iterate_2019_ranked_pictures_of_increment
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
    (hStep : ∀ j : ℕ, 1 ≤ j →
      Proposed2019RankIncrementStep K rules A B κ j)
    (n : ℕ) (hn : 1 ≤ n) :
    Has2019RankedPictureWitness K rules A B C0 κ n := by
  have hAll : ∀ t : ℕ,
      Has2019RankedPictureWitness K rules A B C0 κ (t+1) := by
    intro t
    induction t with
    | zero =>
        exact lemma_2_30_coordinated_rank_zero A B C0
          hA hB hKB hBIrred hHer hC0 κ hArrow
    | succ t ih =>
        obtain ⟨W, hW, D, hD, ⟨f, hf⟩, hDArrow, hDCover, hDRank⟩ := ih
        letI : Finite W := hW
        obtain ⟨Z, hZ, C, hC, ⟨g, hg⟩, hCArrow, hCCover, hCRank⟩ :=
          hStep (t+1) (by omega) D hD hDArrow hDCover hDRank
        have hProj : IsInducedClosedUHomomorphismEmbedding
            rules C C0 (f ∘ g) :=
          inducedClosedMap_comp_2019 hf hg
        have hOutput :
            Has2019RankedPictureWitness K rules A B C0 κ ((t+1)+1) :=
          ⟨Z, hZ, C, hC, ⟨f ∘ g, hProj⟩,
            hCArrow, hCCover, hCRank⟩
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hOutput
  have hnEq : n-1+1 = n := Nat.sub_add_cancel hn
  rw [← hnEq]
  exact hAll (n-1)

/-- The corrected 2019 Lemma 2.31 FINITE-WEAK-TEST conclusion follows
from the explicit higher-rank constructor and the constructed rank-one
base. All weak tests S have their ORIGINAL vertex cardinal bound. -/
theorem lemma_2_31_exact_weak_tests_of_rank_increment
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
    (hStep : ∀ j : ℕ, 1 ≤ j →
      Proposed2019RankIncrementStep K rules A B κ j)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      IsUClosed rules C ∧
      (∃ f : Z → P,
        IsInducedClosedUHomomorphismEmbedding rules C C0 f) ∧
      StructuralRamsey.Arrow A B C κ ∧
      CorrectedUIrreduciblesIn K rules C ∧
      (∀ S : Finset Z, S.card ≤ n →
        HasInducedClosedUKCompletion K rules
          (C.induce (↑S : Set Z))) := by
  obtain ⟨Z, hZ, C, hC, hProj, hCArrow, hCCover, hCRank⟩ :=
    iterate_2019_ranked_pictures_of_increment A B C0
      hA hB hKB hBIrred hHer hC0 κ hArrow hStep n hn
  letI : Finite Z := hZ
  have hAbstractRank : Has2019ClosedRankCompletions K rules C n := by
    intro T hFiniteT hClosedT hSizeT
    letI : Fintype T := hFiniteT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hCRank T hClosedT hSizeT)
  refine ⟨Z, hZ, C, hC, hProj, hCArrow, hCCover, ?_⟩
  exact lemma_2_31_exact_weak_tests_of_closed_rank
    K rules C hC n hAbstractRank

end AllThoseRamseyClasses.Published
