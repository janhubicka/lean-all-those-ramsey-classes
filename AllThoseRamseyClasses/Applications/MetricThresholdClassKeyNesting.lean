import AllThoseRamseyClasses.Applications.MetricFiniteNestedConvexOrder
import AllThoseRamseyClasses.Applications.MetricConvexityTransfer
import Mathlib.Tactic

/-!
# Sorted metric thresholds produce exactly nested class-key lists

The all-level convex-order theorem consumes a finite list of
ordered class labels satisfying NestedLevels. This module
proves the generic metric bridge needed to manufacture that
nesting condition: if each key identifies the threshold
relation d(x,y) ≤ j exactly, then increasing real thresholds
give a nested list from finer to coarser classes.

It also shows how a list containing every proper jump can
cover all JumpConvex requirements. Neither statement constructs
the real class-key maps nor assumes metric completion.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

open AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Threshold equivalence itself forces nestedness of all
successive class-key fibres when the thresholds are increasing.
The keys may live in ANY common label type. -/
theorem thresholdClassKeys_nested
    {X : Type u} {K : Type v}
    (d : X → X → ℝ)
    (key : ℝ → X → K)
    (levels : List ℝ)
    (hIncreasing : levels.Pairwise (· < ·))
    (hExact : ∀ j ∈ levels, ∀ x y : X,
      key j x = key j y ↔ d x y ≤ j) :
    NestedLevels (levels.map key) := by
  induction levels with
  | nil => trivial
  | cons j rest ih =>
      have hHead : ∀ k ∈ rest, j < k := by
        cases hIncreasing with
        | cons hRel _ => exact hRel
      have hTail : rest.Pairwise (· < ·) := by
        cases hIncreasing with
        | cons _ hRest => exact hRest
      have hExactRest : ∀ k ∈ rest, ∀ x y : X,
          key k x = key k y ↔ d x y ≤ k := by
        intro k hk x y
        exact hExact k (by simp [hk]) x y
      constructor
      · intro other hOther x y hxy
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hOther
        have hClose : d x y ≤ j :=
          (hExact j (by simp) x y).mp hxy
        exact (hExactRest k hk x y).mpr
          (hClose.trans (le_of_lt (hHead k hk)))
      · exact ih hTail hExactRest

/-- If the increasing threshold list contains all proper
S-jumps, every required jump-convexity level is represented
by an exact class-key equality relation. -/
theorem thresholdClassKeys_cover
    {X : Type u} {K : Type v}
    (S : Set ℝ) (d : X → X → ℝ)
    (key : ℝ → X → K)
    (levels : List ℝ)
    (hComplete : ∀ j : ℝ, Jump S j → j ∈ levels)
    (hExact : ∀ j ∈ levels, ∀ x y : X,
      key j x = key j y ↔ d x y ≤ j) :
    ∀ j : ℝ, Jump S j →
      ∃ label ∈ levels.map key, ∀ x y : X,
        label x = label y ↔ d x y ≤ j := by
  intro j hj
  refine ⟨key j, List.mem_map.mpr ⟨j, hComplete j hj, rfl⟩, ?_⟩
  exact hExact j (hComplete j hj)

end AllThoseRamseyClasses.Applications.MetricConvexOrder
