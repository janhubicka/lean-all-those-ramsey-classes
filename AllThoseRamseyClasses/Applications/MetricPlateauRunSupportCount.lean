import Mathlib.Tactic

/-!
# Count maximal absorbed runs in an actual prefix-compression mask

The printed metric noncycle argument contracts every inclusion-maximal
contiguous path on which the rounded prefix remains constant.

Encode each later original path EDGE by a Boolean:
* `true`: the edge was absorbed (constant prefix), and is deleted;
* `false`: the rounded prefix strictly increased, and is retained.

The number p of maximal consecutive true runs is at most k+1, where
k is the number of false entries (retained increasing edges).
This is a theorem of arbitrary Boolean lists, not a separate
assumption about the geometry. Consequently if the compressed
ordinary cycle has q=k+2 vertices with q≤|S|, the number
of exposed original vertices when keeping both endpoints of
each contracted run is ≤q+p≤2|S|.

The all-absorbed exceptional case retains a triangle (q=3,p=1)
and its four exposed original vertices fit the same bound if |S|≥2.

A separate source theorem must connect the actual rounded-prefix
compression mask to a list of genuine disjoint paths in the original
cycle. This module proves only the exact finite combinatorial
count, not that external geometric bridge or Ramsey.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Number of strictly increasing (retained) edges. -/
def prefixStrictEdgeCount : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 0 else 1) + prefixStrictEdgeCount bs

/-- Number of starts of maximal absorbed-edge runs. The state
argument records whether the previous edge was absorbed. -/
def prefixPlateauRunCount : Bool → List Bool → ℕ
  | _, [] => 0
  | active, b :: bs =>
      (if b && !active then 1 else 0) +
        prefixPlateauRunCount b bs

/-- Every plateau run after the first requires a retained strict
edge between it and the preceding run. The stronger active-state
version is essential in the induction. -/
theorem prefixPlateauRunCount_bounds (flags : List Bool) :
    prefixPlateauRunCount false flags ≤ prefixStrictEdgeCount flags + 1 ∧
    prefixPlateauRunCount true flags ≤ prefixStrictEdgeCount flags := by
  induction flags with
  | nil =>
      simp [prefixPlateauRunCount, prefixStrictEdgeCount]
  | cons b bs ih =>
      cases b <;>
        simp [prefixPlateauRunCount, prefixStrictEdgeCount] at * <;>
        omega

/-- Actual q+p support bound in the ORDINARY compression case.
Unlike the earlier conditional q/p arithmetic, the p≤k+1
hypothesis is now DERIVED from the true-run combinatorics. -/
theorem prefixPlateauOrdinary_exposed_card_le
    (sCard : ℕ) (flags : List Bool)
    (hCompressed : prefixStrictEdgeCount flags + 2 ≤ sCard) :
    (prefixStrictEdgeCount flags + 2) +
      prefixPlateauRunCount false flags ≤ 2 * sCard := by
  have hRuns := (prefixPlateauRunCount_bounds flags).1
  omega

/-- The printed exceptional one-run triangle has q=3 and p=1.
It preserves the original endpoint cutoff whenever |S|≥2. -/
theorem prefixPlateauExceptional_exposed_card_le
    (sCard : ℕ) (hTwo : 2 ≤ sCard) :
    3 + 1 ≤ 2 * sCard := by
  omega

end AllThoseRamseyClasses.Applications.MetricSaturation
