import AllThoseRamseyClasses.Lifts.FiniteNamedClosedComponentLift
import Mathlib.Data.Fintype.Card

/-!
# Track E2: an unconditional source-cardinality test cutoff

For the alternative finite named forbidden-family lift, we need a
single natural-number cutoff n which dominates the carrier size
of EVERY named forbidden source. The old 2019 regular infinite
family case needs a more delicate control-dependent cutoff.

For a finite named family, use a simple bound: the total number
of all vertices across the disjoint union of the source carriers.
Each individual source injects into that dependent sum.
The sum is finite even when the language has infinitely many
relation symbols and functions of arbitrary arity.

The resulting n is an explicit, choice-independent natural
number from the supplied finite family; it is not assumed as
an external hypothesis. A sharper maximum is possible but is
unnecessary for the local-to-global avoidance theorem.

This lemma asserts neither the existence of a sparse Ramsey
control nor of any ambient-relative weak-test completions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A finite witness to the uniform forbidden-source size bound:
the cardinality of the finite dependent sum of all named sources.
The empty forbidden family has cutoff 0. -/
noncomputable def finiteNamedTotalForbiddenVertexCutoff
    (Family : FiniteNamedFunctionalSources.{u,0} L) : ℕ :=
  Nat.card (Σ i : Family.Index, Family.Carrier i)

/-- Every named forbidden-source carrier embeds in the dependent
sum defining the uniform cutoff, so its cardinality is bounded
by that cutoff. No connectedness, irreducibility or assumptions
on native function arities are used. -/
theorem finiteNamedSource_card_le_totalCutoff
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (i : Family.Index) :
    Nat.card (Family.Carrier i) ≤
      finiteNamedTotalForbiddenVertexCutoff Family := by
  classical
  letI : Finite Family.Index := Family.finiteIndex
  letI (j : Family.Index) : Finite (Family.Carrier j) :=
    Family.finiteCarrier j
  letI : Finite (Σ j : Family.Index, Family.Carrier j) := inferInstance
  have hInj : Function.Injective
      (fun x : Family.Carrier i =>
        (⟨i, x⟩ : Σ j : Family.Index, Family.Carrier j)) := by
    intro x y h
    cases h
    rfl
  exact Nat.card_le_card_of_injective _ hInj

/-- An honest single cutoff n exists for every finite named
forbidden family, including the empty family. This isolates the
numeric side of E2 from the still missing sparse-picture
construction and ambient-relative weak completions. -/
theorem finiteNamedFamily_has_finite_test_cutoff
    (Family : FiniteNamedFunctionalSources.{u,0} L) :
    ∃ n : ℕ, ∀ i : Family.Index,
      Nat.card (Family.Carrier i) ≤ n :=
  ⟨finiteNamedTotalForbiddenVertexCutoff Family,
    finiteNamedSource_card_le_totalCutoff Family⟩

end AllThoseRamseyClasses.Lifts
