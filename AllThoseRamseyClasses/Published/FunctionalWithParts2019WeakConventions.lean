import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Track C: weak-function conventions and the single-valued boundary

The survey displays a CLIPPED weak restriction F^weak(x)=F^A(x) ∩ S;
the exact 2019 OLD tagged formalization used in the corrected two-pass
proof retains only ENTIRE complete output sets, so a value with any
output outside S becomes undefined. These conventions are distinct
for genuinely set-valued functions with partially surviving outputs.

The original published 2019 partial SINGLE-valued function case avoids
this particular divergence: a nonempty output set has at most ONE
element, hence either all outputs survive or none survive.

This file proves both facts for the genuinely partial Option(Set)
representation, also preserving the distinct state some-empty. It
does not assert that the survey's legacy TOTAL set-valued convention
(which uses an empty set for undefinedness) distinguishes none and
some-empty; that additional mismatch remains explicit.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe v
variable {V : Type v}

/-- On an arbitrary set-valued partial function input, a nonempty
output that partly survives S is CLIPPED to a nonempty complete
value by the intersection convention but is declared UNDEFINED by
the whole-fibre convention. The carrier S is unchanged. -/
theorem weakValue_clipped_vs_whole_of_partial_survival
    (S U : Set V)
    (hU : U.Nonempty)
    (hMeet : (U ∩ S).Nonempty)
    (hNotSubset : ¬ U ⊆ S) :
    weakValue S (some U) =
      some {x : S | x.1 ∈ U} ∧
    wholeWeakValue S (some U) = none := by
  constructor
  · simp [weakValue, hU, hMeet]
  · exact wholeWeakValue_of_not_subset S U hNotSubset

/-- When the whole output value is EMPTY or contains at most one
point, clipping and complete-fibre deletion agree exactly (including
defined-empty versus undefined). This is the important boundary
under which the two candidate functional proof conventions coincide. -/
theorem weakValue_eq_wholeWeakValue_of_subsingleton
    (S U : Set V)
    (hSingleton : ∀ x ∈ U, ∀ y ∈ U, x = y) :
    weakValue S (some U) = wholeWeakValue S (some U) := by
  classical
  by_cases hU : U.Nonempty
  · by_cases hSubset : U ⊆ S
    · have hMeet : (U ∩ S).Nonempty := by
        obtain ⟨x, hx⟩ := hU
        exact ⟨x, hx, hSubset hx⟩
      simp [weakValue, wholeWeakValue, hU, hSubset, hMeet]
    · have hNoMeet : ¬ (U ∩ S).Nonempty := by
        rintro ⟨x, hxU, hxS⟩
        apply hSubset
        intro y hyU
        have hEq : y = x := hSingleton y hyU x hxU
        rw [hEq]
        exact hxS
      simp [weakValue, wholeWeakValue, hU, hSubset, hNoMeet]
  · have hEmpty : U = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨x, hx⟩).elim
      · simp
    subst U
    simp [weakValue, wholeWeakValue]

/-- The two genuinely partial weak-value decoders coincide on all
partial SINGLE-valued values, including none and some-empty. This
is a precise value-level bridge; it does not equate the entire
additional OLD ambient domain-mask representation with the graph of
its recomputed weak functional restriction. -/
theorem weakValue_eq_wholeWeakValue_of_singleValued
    (S : Set V) (value : Option (Set V))
    (hValue : ∀ U : Set V, value = some U →
        ∀ x ∈ U, ∀ y ∈ U, x = y) :
    weakValue S value = wholeWeakValue S value := by
  cases hv : value with
  | none =>
      rfl
  | some U =>
      exact weakValue_eq_wholeWeakValue_of_subsingleton
        S U (hValue U hv)

/-- For a genuine partial function structure whose every defined
output contains AT MOST ONE point, clipped and all-or-none weak
restrictions agree on EVERY operation and EVERY exact subset S.

This is the function-level exact matching needed for the published
single-valued case. The relations of the two weak structures also
coincide by definition, independently of this hypothesis. -/
theorem weakInduce_func_eq_wholeWeakInduce_of_singleValued
    {L : Language} (A : PartialSetStructure L V)
    (hSingle : ∀ F xs U, A.func F xs = some U →
      ∀ x ∈ U, ∀ y ∈ U, x = y)
    (S : Set V) (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) :
    (weakInduce A S).func F xs =
      (wholeWeakInduce A S).func F xs := by
  change weakValue S (A.func F (Subtype.val ∘ xs)) =
    wholeWeakValue S (A.func F (Subtype.val ∘ xs))
  exact weakValue_eq_wholeWeakValue_of_singleValued S
    (A.func F (Subtype.val ∘ xs))
    (fun U hU => hSingle F (Subtype.val ∘ xs) U hU)

/-- Relation records are exactly identical under clipped and
whole-fibre weak induction without any assumption on functions. -/
theorem weakInduce_rel_iff_wholeWeakInduce
    {L : Language} (A : PartialSetStructure L V)
    (S : Set V) (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → S) :
    (weakInduce A S).rel R xs ↔
      (wholeWeakInduce A S).rel R xs := by
  rfl

end AllThoseRamseyClasses.Published
