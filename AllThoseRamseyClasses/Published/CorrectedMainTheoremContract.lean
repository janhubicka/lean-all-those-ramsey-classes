import AllThoseRamseyClasses.Published.LiteralWeakRankBridge
import PartiteConstruction.Ramsey.EmptyClosureMultiamalgamation

/-!
# Exact class-level target for the minimally repaired 2019 Theorem 2.18

This file does NOT assert that the corrected theorem is proved.

The class definition below follows the PUBLISHED 2019 clauses
(1)--(3), (4a) and (4c), and changes ONLY the membership clause
(4b) to U-CLOSED U-irreducible tests. All completion maps are the
LITERAL original 2019 U-homomorphism-embeddings, rather than the
experimental weaker closed-test maps.

A conditional final theorem isolates precisely the missing
construction. Given the original Ramsey control C0 and the
local cutoff n(B,C0), one must construct a finite U-closed
Ramsey witness C with:
  - an ORIGINAL 2019 U-completion C -> C0;
  - all U-closed U-irreducible tests in K;
  - ORIGINAL K,U-completions of every weak n-vertex test.
Then the local axiom and the existing verified B-copywise Ramsey
transfer finish the theorem. The sparse witness construction is
a transparent EXPLICIT hypothesis and is NOT disguised as proved.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Exact class-theoretic hypotheses of the preferred one-clause
correction to published Definition 2.17. -/
structure MinimallyCorrectedMultiamalgamationClass
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop where
  subset : ∀ {X : Type v} (C : RelStructure L X), K C → R C
  finite : ∀ {X : Type v} (C : RelStructure L X), K C → Finite X
  closed : ∀ {X : Type v} (C : RelStructure L X),
    K C → IsUClosed rules C
  hereditary : ClosedUHereditary K rules
  strong : HasFiniteStrongAmalgamation K
  localCompletion :
    ∀ {X Y : Type v} [Finite X] [Finite Y]
      (B : RelStructure L X) (C0 : RelStructure L Y),
      K B → R C0 →
      ∃ n : ℕ, CorrectedULocalCompletionAt K rules B C0 n

/-- The actual corrected class-level theorem is this TARGET
proposition, not an axiom and not a proved theorem. -/
def CorrectedTheorem218Target : Prop :=
  ∀ (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L),
    FiniteRamseyClass R →
    (∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible) →
    MinimallyCorrectedMultiamalgamationClass R K rules →
    FiniteRamseyClass K

/-- The complete sparse-Picture output required for the corrected
theorem, with the ORIGINAL map and exact weak tests. -/
def HasCorrectedSparseWitness
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    {UA VB P : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P)
    (n : ℕ)
    (κ : Type) : Prop :=
  ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
    IsUClosed rules C ∧
    IsUCompletion rules C C0 ∧
    CorrectedUIrreduciblesIn K rules C ∧
    (∀ S : Finset Z, S.card ≤ n →
      HasLiteralUKCompletion K rules (C.induce (↑S : Set Z))) ∧
    StructuralRamsey.Arrow A B C κ

/-- A fully explicit conditional endgame for the corrected first
main theorem. No strong-amalgamation or construction result is hidden
in a typeclass: all class assumptions and the missing witness
constructor are written as visible arguments. -/
theorem corrected_multiamalgamation_of_sparse_witnesses
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hK : MinimallyCorrectedMultiamalgamationClass R K rules)
    (hBuild :
      ∀ {UA VB P : Type v} [Finite UA] [Finite VB] [Finite P]
        (A : RelStructure L UA) (B : RelStructure L VB)
        (C0 : RelStructure L P) (n : ℕ)
        (κ : Type) [Fintype κ] [Nonempty κ],
        K A → K B → R C0 →
        StructuralRamsey.Arrow A B C0 κ →
        HasCorrectedSparseWitness K rules A B C0 n κ) :
    FiniteRamseyClass K := by
  intro UA VB hUA hVB A B hA hB κ hκ hκNonempty
  have hRA : R A := hK.subset A hA
  have hRB : R B := hK.subset B hB
  obtain ⟨P, hP, C0, hRC0, hArrow0⟩ :=
    hR A B hRA hRB κ
  letI : Finite P := hP
  obtain ⟨n, hLocal⟩ := hK.localCompletion B C0 hB hRC0
  obtain ⟨Z, hZ, C, hClosed, hControl, hCover, hSmall, hArrow⟩ :=
    hBuild A B C0 n κ hA hB hRC0 hArrow0
  letI : Finite Z := hZ
  exact arrow_of_BCopywiseCompletion_inClass hArrow
    (hLocal C hClosed hControl hCover hSmall)

end AllThoseRamseyClasses.Published
