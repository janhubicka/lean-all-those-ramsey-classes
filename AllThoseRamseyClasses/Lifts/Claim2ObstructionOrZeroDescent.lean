import AllThoseRamseyClasses.Lifts.Claim2ConditionalFiniteChain

/-!
# Track B: a finite selected-Q descent ends at rank zero or a real obstruction

The geometric positive-B-rank dichotomy presently admits two genuine
smaller-root obstructions: old-root capture and an A-mixed component.
We must not silently exclude them when iterating one-sided flips.

This module isolates the valid logical consequence of *conditional*
progress.  In each state satisfying the invariant, a positive rank
must give either (i) old-root capture, (ii) A-mixedness, or (iii) a
supplied genuine step.  The final outcome is rank zero or one of the
two obstructions, with a strict bound on the number of steps.

To instantiate this with original geometric Claim 2, still needed:
a bundled state/step interface for the same actual selected Q,
initial boundary injectivity, the precise positive-rank dichotomy
with all preserved invariants, and any terminal contradiction.
-/

namespace AllThoseRamseyClasses.Lifts

universe u
variable {State : Type u}

/-- The exact quantitative rank invariant for a finite chain of
actually supplied steps. This retains terminal rank, unlike the weaker
length-only estimate. -/
theorem conditionalSelectedQChain_rank_budget
    {step : State → State → Prop} (rank : State → ℕ)
    (hDecrease : ∀ ⦃s t⦄, step s t → rank t < rank s)
    {n : ℕ} {s t : State}
    (hChain : ConditionalSelectedQChain step n s t) :
    n + rank t ≤ rank s := by
  induction hChain with
  | nil s =>
      simp
  | cons hStep hTail ih =>
      have hlt := hDecrease hStep
      omega

/-- A genuine obstruction-sensitive descent theorem.  The progress
hypothesis is *exactly* three-way and is used only at positive rank.
This theorem proves neither that positive-rank progress holds for the
original Claim 2 nor that its two obstructions are impossible.

Every step must preserve `good`; the final state and its rank are
witnessed explicitly by a finite chain of the actual `step` relation. -/
theorem conditionalSelectedQChain_reaches_zero_or_two_obstructions
    {step : State → State → Prop}
    (rank : State → ℕ)
    (good oldRootCapture aMixed : State → Prop)
    (hDecrease : ∀ ⦃s t⦄, step s t → rank t < rank s)
    (hPreserves : ∀ ⦃s t⦄, step s t → good s → good t)
    (hProgress : ∀ s, good s → 0 < rank s →
      oldRootCapture s ∨ aMixed s ∨ ∃ t, step s t)
    (s₀ : State) (h₀ : good s₀) :
    ∃ (k : ℕ) (s : State),
      ConditionalSelectedQChain step k s₀ s ∧
      good s ∧
      (rank s = 0 ∨ oldRootCapture s ∨ aMixed s) ∧
      k + rank s ≤ rank s₀ := by
  have hAux : ∀ (m : ℕ) (s₀ : State),
      rank s₀ = m → good s₀ →
      ∃ (k : ℕ) (s : State),
        ConditionalSelectedQChain step k s₀ s ∧
        good s ∧
        (rank s = 0 ∨ oldRootCapture s ∨ aMixed s) ∧
        k + rank s ≤ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro s hrs hg
        by_cases hz : rank s = 0
        · refine ⟨0, s, ConditionalSelectedQChain.nil s, hg, Or.inl hz, ?_⟩
          omega
        · have hp : 0 < rank s := by omega
          rcases hProgress s hg hp with hc | hm | ⟨t, hStep⟩
          · refine ⟨0, s, ConditionalSelectedQChain.nil s, hg,
                Or.inr (Or.inl hc), ?_⟩
            omega
          · refine ⟨0, s, ConditionalSelectedQChain.nil s, hg,
                Or.inr (Or.inr hm), ?_⟩
            omega
          · have hlt : rank t < m := by
              have hStepDecrease := hDecrease hStep
              omega
            obtain ⟨k, u, hTail, hu, hExit, hBudget⟩ :=
              ih (rank t) hlt t rfl (hPreserves hStep hg)
            refine ⟨k + 1, u, ConditionalSelectedQChain.cons hStep hTail,
              hu, hExit, ?_⟩
            have hStepDecrease := hDecrease hStep
            omega
  exact hAux (rank s₀) s₀ rfl h₀

/-- If both genuine smaller-root obstructions are separately
eliminated on ALL admissible states, conditional progress reaches rank
zero. The absence of those obstructions is a premise, not a theorem. -/
theorem conditionalSelectedQChain_reaches_zero_of_no_obstructions
    {step : State → State → Prop}
    (rank : State → ℕ)
    (good oldRootCapture aMixed : State → Prop)
    (hDecrease : ∀ ⦃s t⦄, step s t → rank t < rank s)
    (hPreserves : ∀ ⦃s t⦄, step s t → good s → good t)
    (hProgress : ∀ s, good s → 0 < rank s →
      oldRootCapture s ∨ aMixed s ∨ ∃ t, step s t)
    (hNoCapture : ∀ s, good s → ¬ oldRootCapture s)
    (hNoMixed : ∀ s, good s → ¬ aMixed s)
    (s₀ : State) (h₀ : good s₀) :
    ∃ (k : ℕ) (s : State),
      ConditionalSelectedQChain step k s₀ s ∧
      good s ∧ rank s = 0 ∧ k ≤ rank s₀ := by
  obtain ⟨k, s, hChain, hg, hExit, hBudget⟩ :=
    conditionalSelectedQChain_reaches_zero_or_two_obstructions
      rank good oldRootCapture aMixed
      hDecrease hPreserves hProgress s₀ h₀
  rcases hExit with hz | hc | hm
  · refine ⟨k, s, hChain, hg, hz, ?_⟩
    omega
  · exact False.elim ((hNoCapture s hg) hc)
  · exact False.elim ((hNoMixed s hg) hm)

end AllThoseRamseyClasses.Lifts
