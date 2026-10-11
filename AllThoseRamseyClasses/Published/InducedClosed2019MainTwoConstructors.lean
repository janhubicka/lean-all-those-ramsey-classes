import AllThoseRamseyClasses.Published.InducedClosed2019Lemma231Iteration
import AllThoseRamseyClasses.Published.InducedClosed2019ClassEquivalence
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer

/-!
# Repaired 2019 Theorem 2.18: reduce to exactly TWO Picture constructors

The source of the 2019 proof uses two nontrivial constructions:

  (I) the unrestricted initial, potentially NON-U-CLOSED control
      Picture of Lemma 2.28, producing a CLOSED Ramsey witness;
  (II) the genuine higher-rank j -> j+1 Picture increment of
      Lemma 2.30 for j>=1.

Both remain explicit theorem ARGUMENTS below. The native rank-zero
construction, finite iteration of Lemma 2.31, the exact weak-test
transfer, composition of corrected positive projections and the
local-completion/colouring endgame are all separately Lean-checked.

This is a materially sharper contract than assuming outright the
whole final sparse Ramsey witness. It follows the published 2019
proof order, its fixed n(B,C0) quantifier, and the proposed coordinated
Definition 2.15 + Definition 2.17(4b) repair precisely.

The initial control C0 is only a member of the Ramsey class R,
not assumed U-closed. It is ordinarily irreducible because of R,
so local finiteness (4a) is applicable after both constructions.

No positive proof of the missing constructors or of the unconditional
general corrected Theorem 2.18 is claimed in this file.
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

/-- The proposed corrected 2019 Theorem 2.18 follows, via the
EXACT sequence of Lemmas 2.28, 2.30 and 2.31, if and ONLY IF the two
missing positive constructors are supplied as explicit premises:
the unrestricted initial Picture and rank increments for j>=1.

More precisely, the implication from these constructors is proved;
the converse (or existence of either constructor) is NOT asserted.

All available Lean-certified work, including the true rank-zero
base and the original exact weak-test n-vertex requirement, is used.
No unproved construction appears as an axiom or implicit instance. -/
theorem coordinated2019_ramsey_of_two_picture_constructors
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules)
    (hInitial :
      ∀ {X Y Z : Type v} [Finite X] [Finite Y] [Finite Z]
        (A : RelStructure L X) (B : RelStructure L Y)
        (C0 : RelStructure L Z)
        (κ : Type*) [Fintype κ] [Nonempty κ],
        K A → K B → R C0 →
        StructuralRamsey.Arrow A B C0 κ →
        Has2019UnrestrictedInitialPicture K rules A B C0 κ)
    (hHigher :
      ∀ {X Y : Type v} [Finite X] [Finite Y]
        (A : RelStructure L X) (B : RelStructure L Y)
        (κ : Type*) [Fintype κ] [Nonempty κ]
        (j : ℕ), 1 ≤ j → K A → K B →
        Proposed2019RankIncrementStep K rules A B κ j) :
    FiniteRamseyClass K := by
  intro X Y hFiniteX hFiniteY A B hKA hKB κ hκ hκNonempty
  have hRA : R A := hK.induced.subset A hKA
  have hRB : R B := hK.induced.subset B hKB
  have hAClosed : IsUClosed rules A := hK.induced.closed A hKA
  have hBClosed : IsUClosed rules B := hK.induced.closed B hKB
  have hBIrred : B.Irreducible := hRIrred B hRB
  have hHer : ClosedUHereditary K rules :=
    embeddedClosedHereditary_of_induced
      hK.induced.hereditary hK.iso
  obtain ⟨Z, hZ, C0, hRC0, hArrow0⟩ :=
    hR A B hRA hRB κ
  letI : Finite Z := hZ
  obtain ⟨n, hLocal⟩ :=
    hK.induced.localCompletion B C0 hKB hRC0
  obtain ⟨W, hW, D, hDClosed, hInitialMap, hArrowD, hCoveredD⟩ :=
    hInitial A B C0 κ hKA hKB hRC0 hArrow0
  letI : Finite W := hW
  obtain ⟨p0, hp0⟩ := hInitialMap
  have hRankStep : ∀ j : ℕ, 1 ≤ j →
      Proposed2019RankIncrementStep K rules A B κ j := by
    intro j hj
    exact hHigher A B κ j hj hKA hKB
  obtain ⟨T, hT, C, hCClosed, hSecondMap,
      hArrowC, hCoveredC, hWeakTests⟩ :=
    lemma_2_31_exact_weak_tests_of_rank_increment A B D
      hAClosed hBClosed hKB hBIrred hHer
      hDClosed κ hArrowD hRankStep (n+1) (by omega)
  letI : Finite T := hT
  obtain ⟨p1, hp1⟩ := hSecondMap
  have hTotalMap :
      IsInducedClosedUHomomorphismEmbedding rules C C0 (p0 ∘ p1) :=
    inducedClosedMap_comp_2019 hp0 hp1
  have hCopywise : HasCopywiseCompletion K B C :=
    hLocal C hCClosed
      ⟨hRIrred C0 hRC0, p0 ∘ p1, hTotalMap⟩
      hCoveredC
      (fun S hS => hWeakTests S (by omega))
  exact arrow_of_BCopywiseCompletion_inClass hArrowC hCopywise

end AllThoseRamseyClasses.Published
