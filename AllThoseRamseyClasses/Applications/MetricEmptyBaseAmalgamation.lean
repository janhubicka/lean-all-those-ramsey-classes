import AllThoseRamseyClasses.Applications.MetricJumpSamedist
import Mathlib.Tactic

/-!
# S-metric amalgamation over an empty base

The cross-side distance is the MAXIMUM M of a nonempty finite set S,
not the minimum of an empty family of base path lengths.

This module verifies an actual S-metric on the disjoint union of two
S-metric spaces. The within-side distances are unchanged, and all
cross-side distances are M. Because the manuscript's jumps are PROPER
(j<M), no jump threshold class can meet both sides.

This is the empty-base branch of the strong-amalgamation application,
not the general common-base or ordered functional amalgamation.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Distances within either side are unchanged; every cross
distance is the shared maximal allowed S-distance. -/
def separatedSumDistance {U : Type u} {V : Type v}
    (m : ℝ) (dU : U → U → ℝ) (dV : V → V → ℝ) :
    (U ⊕ V) → (U ⊕ V) → ℝ
  | .inl a, .inl b => dU a b
  | .inr a, .inr b => dV a b
  | .inl _, .inr _ => m
  | .inr _, .inl _ => m

/-- Every distance of an S-metric is nonnegative when S consists
of positive reals. -/
private theorem metric_distance_nonneg {S : Set ℝ}
    {V : Type v} (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d) (x y : V) :
    0 ≤ d x y := by
  rcases metric_value_mem hd x y with hz | hs
  · rw [hz]
  · exact (hpos (d x y) hs).le

/-- Every metric distance is at most a common upper bound m for S,
provided m is nonnegative, including diagonal zero. -/
private theorem metric_distance_le_max {S : Set ℝ}
    {V : Type v}
    (hm0 : 0 ≤ m) (hmax : ∀ s ∈ S, s ≤ m)
    {d : V → V → ℝ} (hd : MetricOn S d) (x y : V) :
    d x y ≤ m := by
  rcases metric_value_mem hd x y with hz | hs
  · rw [hz]
    exact hm0
  · exact hmax _ hs

/-- The actual disjoint-union gluing metric for an empty amalgamation
base, with *no identification of vertices* and all old distances
unchanged. The maximum is explicitly in S and bounds S. -/
theorem separatedSumDistance_metric {S : Set ℝ}
    {U : Type u} {V : Type v}
    (hpos : Positive S) (m : ℝ) (hm : m ∈ S)
    (hmax : ∀ s ∈ S, s ≤ m)
    {dU : U → U → ℝ} (hdU : MetricOn S dU)
    {dV : V → V → ℝ} (hdV : MetricOn S dV) :
    MetricOn S (separatedSumDistance m dU dV) := by
  have hm0 : 0 ≤ m := (hpos m hm).le
  have hU0 : ∀ a b : U, 0 ≤ dU a b :=
    metric_distance_nonneg hpos hdU
  have hV0 : ∀ a b : V, 0 ≤ dV a b :=
    metric_distance_nonneg hpos hdV
  have hUmax : ∀ a b : U, dU a b ≤ m :=
    metric_distance_le_max hm0 hmax hdU
  have hVmax : ∀ a b : V, dV a b ≤ m :=
    metric_distance_le_max hm0 hmax hdV
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | inl a => exact hdU.diag a
    | inr a => exact hdV.diag a
  · intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            exact hdU.values a b (by
              intro hab
              exact hxy (congrArg Sum.inl hab))
        | inr b => exact hm
    | inr a =>
        cases y with
        | inl b => exact hm
        | inr b =>
            exact hdV.values a b (by
              intro hab
              exact hxy (congrArg Sum.inr hab))
  · intro x y
    cases x with
    | inl a =>
        cases y with
        | inl b => exact hdU.symm a b
        | inr b => rfl
    | inr a =>
        cases y with
        | inl b => rfl
        | inr b => exact hdV.symm a b
  · intro x y z
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            cases z with
            | inl c => exact hdU.triangle a b c
            | inr c =>
                change m ≤ dU a b + m
                linarith [hU0 a b]
        | inr b =>
            cases z with
            | inl c =>
                change dU a c ≤ m + m
                linarith [hUmax a c]
            | inr c =>
                change m ≤ m + dV b c
                linarith [hV0 b c]
    | inr a =>
        cases y with
        | inl b =>
            cases z with
            | inl c =>
                change m ≤ m + dU b c
                linarith [hU0 b c]
            | inr c =>
                change dV a c ≤ m + m
                linarith [hVmax a c]
        | inr b =>
            cases z with
            | inl c =>
                change m ≤ dV a b + m
                linarith [hV0 a b]
            | inr c => exact hdV.triangle a b c

/-- The maximum of S is never a PROPER jump: by definition a jump
has a larger allowed distance above it. -/
theorem jump_lt_max {S : Set ℝ} {m j : ℝ}
    (hmax : ∀ s ∈ S, s ≤ m)
    (hj : Jump S j) : j < m := by
  obtain ⟨b, hb, hjb⟩ := hj.2.1
  exact hjb.trans_le (hmax b hb)

/-- Threshold-equivalence classes at a proper jump cannot cross
the two summands of a disjoint metric amalgamation. -/
theorem separated_cross_not_jump {S : Set ℝ}
    {U : Type u} {V : Type v}
    (m j : ℝ) (hmax : ∀ s ∈ S, s ≤ m)
    (hj : Jump S j)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (x : U) (y : V) :
    ¬ separatedSumDistance m dU dV (.inl x) (.inr y) ≤ j := by
  change ¬ m ≤ j
  exact not_le.mpr (jump_lt_max hmax hj)

end AllThoseRamseyClasses.Applications.MetricSaturation
