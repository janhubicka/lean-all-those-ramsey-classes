import Mathlib

/-!
# Track B: conditional finite-chain preservation and rank bound

This elementary kernel is deliberately independent of any claim that
an eligible selected-Q step exists.  It packages what can legitimately
be iterated once the geometric one-step theorem supplies:
* strict decrease of literal B-exclusive SOURCE rank;
* preservation of the chosen root/boundary/global-symbol invariant.

It does not manufacture the initial invariant, remove smaller-root
capture/A-mixedness, or prove the original minimizer contradiction.
-/

namespace AllThoseRamseyClasses.Lifts

universe u
variable {State : Type u}

/-- A finite chain of *actual* chosen successor steps.  Distinct from
a proof that a successor is available at every positive rank. -/
inductive ConditionalSelectedQChain (step : State → State → Prop) :
    ℕ → State → State → Prop where
  | nil (s : State) : ConditionalSelectedQChain step 0 s s
  | cons {n : ℕ} {s t u : State} :
      step s t →
      ConditionalSelectedQChain step n t u →
      ConditionalSelectedQChain step (n + 1) s u

/-- Every invariant carried through each actual step survives through
any finite chain; existence and initialization remain separate. -/
theorem conditionalSelectedQChain_preserves
    {step : State → State → Prop} {good : State → Prop}
    (hPres : ∀ ⦃s t⦄, step s t → good s → good t)
    {n : ℕ} {s t : State}
    (hChain : ConditionalSelectedQChain step n s t)
    (hGood : good s) : good t := by
  induction hChain with
  | nil s =>
      exact hGood
  | cons hStep hTail ih =>
      exact ih (hPres hStep hGood)

/-- A strict descent chain of literal source ranks cannot have more
steps than its initial rank.  In particular, this is NOT a proof of an
eligible next step at positive rank. -/
theorem conditionalSelectedQChain_length_le_rank
    {step : State → State → Prop} (rank : State → ℕ)
    (hDecrease : ∀ ⦃s t⦄, step s t → rank t < rank s)
    {n : ℕ} {s t : State}
    (hChain : ConditionalSelectedQChain step n s t) :
    n ≤ rank s := by
  induction hChain with
  | nil s =>
      exact Nat.zero_le _
  | cons hStep hTail ih =>
      have hlt := hDecrease hStep
      omega

/-- A positive-length strict descent chain cannot start at zero
B-exclusive SOURCE rank. -/
theorem conditionalSelectedQChain_zero_rank_only_empty
    {step : State → State → Prop} (rank : State → ℕ)
    (hDecrease : ∀ ⦃s t⦄, step s t → rank t < rank s)
    {n : ℕ} {s t : State}
    (hChain : ConditionalSelectedQChain step n s t)
    (hZero : rank s = 0) : n = 0 := by
  have hBound :=
    conditionalSelectedQChain_length_le_rank rank hDecrease hChain
  omega

end AllThoseRamseyClasses.Lifts
