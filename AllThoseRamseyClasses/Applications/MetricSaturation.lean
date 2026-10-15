import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Stabilization of capped S-distance powers

This is a component of the finite-distance reduction in manuscript
`prop:Smetric`. It uses the actual operation
`a ⊕_S b = sSup {s ∈ S | s ≤ a + b}`, not an abstract operation
whose stabilization is assumed.

For a positive generator `a` and a cap `m ∈ S`, all powers stay in
`S ∩ (-∞, m]`. Let `l` be their real supremum. Choose a power `x`
with `l - a < x`. Every power is then a candidate for the next
rounded sum, so the next power is a maximum of the entire sequence.
The sequence stabilizes at that maximum.

No topological closedness of S, finite block count, associativity,
nor commutativity is needed for this one-generator result. The only
well-definedness assumption is that the displayed supremum belongs
to S when its two operands do. Finite generation from several
generators additionally needs the separate associative/commutative
normal-form argument. This file does not prove a metric Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The paper's rounded distance sum, before capping. -/
noncomputable def distanceSum (S : Set ℝ) (a b : ℝ) : ℝ :=
  sSup {s : ℝ | s ∈ S ∧ s ≤ a + b}

/-- The supremum defining the rounded sum is an allowed distance. -/
def WellDefined (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, distanceSum S a b ∈ S

/-- The capped operation used in the finite-distance reduction. -/
noncomputable def cappedSum (S : Set ℝ) (m a b : ℝ) : ℝ :=
  min m (distanceSum S a b)

/-- Every allowed distance below both the cap and the ordinary sum
is below the capped rounded sum. -/
theorem le_cappedSum {S : Set ℝ} {m a b s : ℝ}
    (hs : s ∈ S) (hsm : s ≤ m) (hsab : s ≤ a + b) :
    s ≤ cappedSum S m a b := by
  apply le_min hsm
  exact le_csSup ⟨a + b, fun _ ht => ht.2⟩ ⟨hs, hsab⟩

/-- Capping at an allowed distance preserves allowed distances. -/
theorem cappedSum_mem {S : Set ℝ} {m a b : ℝ}
    (hS : WellDefined S) (hm : m ∈ S) (ha : a ∈ S) (hb : b ∈ S) :
    cappedSum S m a b ∈ S := by
  rcases le_total m (distanceSum S a b) with h | h
  · simpa only [cappedSum, min_eq_left h] using hm
  · simpa only [cappedSum, min_eq_right h] using hS a ha b hb

/-- Index zero is the first positive power, not a neutral element. -/
noncomputable def power (S : Set ℝ) (m a : ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => cappedSum S m (power S m a n) a

/-- All positive powers lie in the allowed bounded distance set. -/
theorem power_mem_le {S : Set ℝ} {m a : ℝ}
    (hS : WellDefined S) (hm : m ∈ S) (ha : a ∈ S) (ham : a ≤ m)
    (n : ℕ) : power S m a n ∈ S ∧ power S m a n ≤ m := by
  induction n with
  | zero => exact ⟨ha, ham⟩
  | succ n ih =>
      exact ⟨cappedSum_mem hS hm ih.1 ha, min_le_left _ _⟩

/-- A positive generator makes its capped powers nondecreasing. -/
theorem power_le_succ {S : Set ℝ} {m a : ℝ}
    (hS : WellDefined S) (hm : m ∈ S) (ha : a ∈ S)
    (ha_pos : 0 < a) (ham : a ≤ m) (n : ℕ) :
    power S m a n ≤ power S m a (n + 1) := by
  have hn := power_mem_le hS hm ha ham n
  exact le_cappedSum hn.1 hn.2 (by linarith)

/-- The sequence reaches its supremum: one power dominates all powers.
This direct maximum argument avoids a strict-increase contradiction. -/
theorem exists_power_max {S : Set ℝ} {m a : ℝ}
    (hS : WellDefined S) (hm : m ∈ S) (ha : a ∈ S)
    (ha_pos : 0 < a) (ham : a ≤ m) :
    ∃ N : ℕ, ∀ k : ℕ, power S m a k ≤ power S m a N := by
  let l : ℝ := sSup (Set.range (power S m a))
  have hb : BddAbove (Set.range (power S m a)) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (power_mem_le hS hm ha ham n).2
  have hl : ∀ n : ℕ, power S m a n ≤ l := by
    intro n
    exact le_csSup hb ⟨n, rfl⟩
  have hnear : ∃ n : ℕ, l - a < power S m a n := by
    by_contra h
    push Not at h
    have hne : (Set.range (power S m a)).Nonempty :=
      ⟨power S m a 0, ⟨0, rfl⟩⟩
    have hupper : l ≤ l - a := by
      change sSup (Set.range (power S m a)) ≤ l - a
      apply csSup_le hne
      rintro _ ⟨n, rfl⟩
      exact h n
    linarith
  obtain ⟨n, hn⟩ := hnear
  refine ⟨n + 1, fun k => ?_⟩
  have hk := power_mem_le hS hm ha ham k
  exact le_cappedSum hk.1 hk.2 (by linarith [hl k])

/-- Some two consecutive positive powers agree. -/
theorem exists_power_stable {S : Set ℝ} {m a : ℝ}
    (hS : WellDefined S) (hm : m ∈ S) (ha : a ∈ S)
    (ha_pos : 0 < a) (ham : a ≤ m) :
    ∃ N : ℕ, power S m a (N + 1) = power S m a N := by
  obtain ⟨N, hN⟩ := exists_power_max hS hm ha ha_pos ham
  exact ⟨N, le_antisymm (hN (N + 1))
    (power_le_succ hS hm ha ha_pos ham N)⟩

/-- Equality of consecutive powers makes the entire tail constant.
This is a recursion fact; no extra algebraic laws are required. -/
theorem power_eq_of_stable {S : Set ℝ} {m a : ℝ} {N : ℕ}
    (hN : power S m a (N + 1) = power S m a N) (k : ℕ) :
    power S m a (N + k) = power S m a N := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change cappedSum S m (power S m a (N + k)) a = power S m a N
      rw [ih]
      exact hN

/-- The set of positive powers of each bounded positive generator is finite. -/
theorem finite_range_power {S : Set ℝ} {m a : ℝ}
    (hS : WellDefined S) (hm : m ∈ S) (ha : a ∈ S)
    (ha_pos : 0 < a) (ham : a ≤ m) :
    (Set.range (power S m a)).Finite := by
  obtain ⟨N, hN⟩ := exists_power_stable hS hm ha ha_pos ham
  apply (Set.finite_range (fun n : Fin (N + 1) => power S m a n)).subset
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ≤ N
  · exact ⟨⟨n, by omega⟩, rfl⟩
  · refine ⟨⟨N, Nat.lt_succ_self N⟩, ?_⟩
    change power S m a N = power S m a n
    have heq : N + (n - N) = n := by omega
    symm
    rw [← heq]
    exact power_eq_of_stable hN (n - N)

end AllThoseRamseyClasses.Applications.MetricSaturation
