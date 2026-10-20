import AllThoseRamseyClasses.Applications.MetricConvexityTransfer
import AllThoseRamseyClasses.Applications.MetricJumpSamedist

/-!
# Relative order of distinct convex jump-equivalence classes

For a convexly ordered S-metric space, the relative order of two
different j-classes is determined by ANY representatives. The
proof is elementary but useful in the metric strong amalgam:
one cannot interchange or interleave the whole classes while
preserving the old order.

This is the missing compatibility lemma for amalgamating the
ordered child lists of the nested jump-class hierarchy.
No finite-S assumption or fixed class-minimum choices are
needed here: the j-threshold is a proper jump and its
transitivity was already established for genuine S-metrics.

In particular the proof must not identify the original
root-cut ordering of INDIVIDUAL vertices with a jump-convex
amalgamation order; the latter is a separate construction.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Two disjoint convex j-classes cannot interleave:
if one representative x precedes y, every member x' of
x's class precedes every member y' of y's class. -/
theorem jumpConvex_disjoint_classes_order
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (hconv : JumpConvex S d)
    (j : ℝ) (hj : Jump S j)
    (x x' y y' : V)
    (hxx' : d x x' ≤ j)
    (hyy' : d y y' ≤ j)
    (hNotXY : ¬ d x y ≤ j)
    (hxy : x < y) :
    x' < y' := by
  by_contra h
  have hy'x' : y' ≤ x' := le_of_not_gt h
  have hy'y : d y' y ≤ j := by
    rw [hd.symm y' y]
    exact hyy'
  by_cases hx_y' : x ≤ y'
  · have hxy' : d x y' ≤ j :=
      (hconv j hj x y' x' hx_y' hy'x' hxx').1
    have hBad : d x y ≤ j :=
      metric_jump_threshold_trans hpos hS hd (Or.inr hj)
        x y' y hxy' hy'y
    exact hNotXY hBad
  · have hy'_x : y' ≤ x := le_of_not_ge hx_y'
    have hy'x : d y' x ≤ j :=
      (hconv j hj y' x y hy'_x (le_of_lt hxy) hy'y).1
    have hxy' : d x y' ≤ j := by
      rw [hd.symm x y']
      exact hy'x
    have hBad : d x y ≤ j :=
      metric_jump_threshold_trans hpos hS hd (Or.inr hj)
        x y' y hxy' hy'y
    exact hNotXY hBad

end AllThoseRamseyClasses.Applications.MetricSaturation
