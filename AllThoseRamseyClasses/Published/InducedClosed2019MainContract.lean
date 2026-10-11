import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer

/-!
# The coordinated 2019 Theorem 2.18: exact induced-test proof contract

Unlike the earlier one-clause CorrectedMainTheoremContract, the proposed
2019 repair changes the MAP predicate of Definition 2.15 together with
the membership clause of Definition 2.17(4b).

This file retains the PAPER'S quantifiers on exact induced substructures:
* intrinsic U-irreducibility is unchanged;
* map tests are simultaneously U-closed and U-irreducible;
* C0 is not required to be U-closed;
* the cutoff n is selected for B,C0 BEFORE a Ramsey candidate C;
* (4c) covers EVERY weak induced subset S with S.card <= n;
* final completion respects copies of B, not all of C.

The first theorem below isolates the missing sparse-Picture constructor.
Its constructor premise is an EXPLICIT proposition, not a theorem, axiom,
class instance, or proof of Theorem 2.18. The second theorem transfers
an independently obtained ABSTRACT protected rank invariant through the
precise induced local axiom; no higher-rank increment is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Definition 2.17 with the proposed COORDINATED repair, using the
paper's actual induced-substructure quantifiers rather than silently
identifying them with an abstract embedded-test convention. -/
structure InducedClosed2019MultiamalgamationClass
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop where
  subset : ∀ {X : Type v} (A : RelStructure L X), K A → R A
  finite : ∀ {X : Type v} (A : RelStructure L X), K A → Finite X
  closed : ∀ {X : Type v} (A : RelStructure L X),
    K A → IsUClosed rules A
  hereditary : ClosedUHereditary K rules
  strong : HasFiniteStrongAmalgamation K
  localCompletion :
    ∀ {X Y : Type v} [Finite X] [Finite Y]
      (B : RelStructure L X) (C0 : RelStructure L Y),
      K B → R C0 →
      ∃ n : ℕ, InducedClosedULocalCompletionAt K rules B C0 n

/-- The positive theorem proposed as a repair of 2019 Theorem 2.18.
This is a TARGET proposition, not proved here. -/
def InducedClosed2019Theorem218Target : Prop :=
  ∀ (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L),
    FiniteRamseyClass R →
    (∀ {X : Type v} (A : RelStructure L X),
      R A → A.Irreducible) →
    InducedClosed2019MultiamalgamationClass R K rules →
    FiniteRamseyClass K

/-- The exact finite output of the still-missing repaired 2019
partite/Picture construction. Every small test is the ORIGINAL
induced vertex set and is allowed to be nonclosed. -/
def HasInducedClosed2019SparseWitness
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    {UA VB P : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P)
    (n : ℕ) (κ : Type) : Prop :=
  ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
    IsUClosed rules C ∧
    (∃ f : Z → P,
      IsInducedClosedUHomomorphismEmbedding rules C C0 f) ∧
    CorrectedUIrreduciblesIn K rules C ∧
    (∀ S : Finset Z, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set Z))) ∧
    StructuralRamsey.Arrow A B C κ

/-- Exact positive endgame with the missing construction displayed
as a hypothesis. The proof applies Definition 2.17(4) at the fixed
n(B,C0), then the original B-copywise Ramsey transfer.

No assertion about the existence of the construction is made. -/
theorem inducedClosed2019_ramsey_of_sparse_witnesses
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRirr : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : InducedClosed2019MultiamalgamationClass R K rules)
    (hBuild :
      ∀ {UA VB P : Type v} [Finite UA] [Finite VB] [Finite P]
        (A : RelStructure L UA) (B : RelStructure L VB)
        (C0 : RelStructure L P) (n : ℕ)
        (κ : Type) [Fintype κ] [Nonempty κ],
        K A → K B → R C0 →
        StructuralRamsey.Arrow A B C0 κ →
        HasInducedClosed2019SparseWitness K rules A B C0 n κ) :
    FiniteRamseyClass K := by
  intro UA VB hUA hVB A B hA hB κ hκ hκNonempty
  have hRA : R A := hK.subset A hA
  have hRB : R B := hK.subset B hB
  obtain ⟨P, hP, C0, hRC0, hArrow0⟩ :=
    hR A B hRA hRB κ
  letI : Finite P := hP
  obtain ⟨n, hLocal⟩ := hK.localCompletion B C0 hB hRC0
  obtain ⟨Z, hZ, C, hClosed, f, hf, hCover, hSmall, hArrow⟩ :=
    hBuild A B C0 n κ hA hB hRC0 hArrow0
  letI : Finite Z := hZ
  exact arrow_of_BCopywiseCompletion_inClass hArrow
    (hLocal C hClosed ⟨hRirr C0 hRC0, f, hf⟩ hCover hSmall)

/-- Reuse the checked abstract rank-to-weak-tests and copywise
transfer lemmas for an EXACT induced-local axiom. The abstract
embedding version is used only as a derived consequence, not
substituted into Definition 2.17.

The entire higher-rank invariant remains an explicit assumption. -/
theorem inducedClosed2019_rank_transfer
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UA VB P Z : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P) (C : RelStructure L Z)
    [Finite Z] (n : ℕ) (κ : Type) [Nonempty κ]
    (hLocal : InducedClosedULocalCompletionAt K rules B C0 n)
    (hHer : ClosedUHereditary K rules) (hB : K B)
    (hClosed : IsUClosed rules C)
    (hC0 : C0.Irreducible)
    (f : Z → P) (hf : IsClosedUHomomorphismEmbedding rules C C0 f)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (hRank : ∀ (T : Set Z) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ n →
      HasClosedUKCompletion K rules (C.induce T))
    (hArrow : StructuralRamsey.Arrow A B C κ) :
    ∃ (X : Type v) (_ : Finite X) (D : RelStructure L X),
      K D ∧ StructuralRamsey.Arrow A B D κ := by
  exact ramsey_of_closedLocalCompletionAt_rank_and_coverage
    A B C0 C n κ hLocal.toAbstractClosed
    hHer hB hClosed hC0 f hf hCover hRank hArrow

end AllThoseRamseyClasses.Published
