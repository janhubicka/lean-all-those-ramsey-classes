import AllThoseRamseyClasses.Applications.MetricRootedAmalgamTriangle
import AllThoseRamseyClasses.Applications.MetricRootedAmalgamSideIsometries
import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossGeometry
import Mathlib.Tactic

/-!
# Exact common-root witness for jump equivalence across metric sides

For the GENUINE finite identified-root S-metric pushout, a vertex
from the first side and a vertex from the second side are within
a proper jump j exactly if some common base vertex lies within
j of both. This holds also if either endpoint itself lies on
the base, not merely for the two off-base private sorts.

The forward argument splits only on original base membership.
When both points lie off the base, use the already certified
finite attained shortest-path j-crossing theorem. The reverse
argument uses the actual proved pushout MetricOn structure and
the idempotence of proper jump thresholds. Old-side isometries
and literal root agreement are used, never assumed implicitly.

This is the root-witness input for amalgamating nested convex
jump classes. It does NOT construct an order or a function F_j.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

private theorem metricRootedLeft_outside
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (x : MetricOutsideRoot iU) :
    metricRootedLeft iU iV hiU x.val =
      (.inr (.inl x) : MetricRootedAmalgamVertex iU iV) := by
  unfold metricRootedLeft
  rw [← metricSideEquiv_inr iU hiU x,
    (metricSideEquiv iU hiU).symm_apply_apply]
  rfl

private theorem metricRootedRight_outside
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (z : MetricOutsideRoot iV) :
    metricRootedRight iU iV hiV z.val =
      (.inr (.inr z) : MetricRootedAmalgamVertex iU iV) := by
  unfold metricRootedRight
  rw [← metricSideEquiv_inr iV hiV z,
    (metricSideEquiv iV hiV).symm_apply_apply]
  rfl

/-- For ANY endpoints belonging to the two ORIGINAL metric
sides (possibly base vertices), jump-close in the glued
metric iff both are jump-close to a common base vertex. -/
theorem metricRootedCross_le_jump_iff_root
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (j : ℝ) (hj : Jump S j)
    (x : U) (z : V) :
    metricRootedShortestDistance S iU iV dU dV
      (metricRootedLeft iU iV hiU x)
      (metricRootedRight iU iV hiV z) ≤ j ↔
      ∃ a : A, dU x (iU a) ≤ j ∧ dV (iV a) z ≤ j := by
  constructor
  · intro h
    by_cases hx : ∃ a : A, iU a = x
    · obtain ⟨a, rfl⟩ := hx
      have hRoot :=
        metricRooted_sides_agree_on_root iU iV hiU hiV a
      rw [hRoot,
        metricRootedShortestDistance_right_isometry S iU iV hiV
          dU dV hBase (iV a) z] at h
      refine ⟨a, ?_, h⟩
      rw [hdU.diag]
      exact (hpos j hj.1).le
    · by_cases hz : ∃ a : A, iV a = z
      · obtain ⟨a, rfl⟩ := hz
        have hRoot :=
          metricRooted_sides_agree_on_root iU iV hiU hiV a
        rw [← hRoot,
          metricRootedShortestDistance_left_isometry S iU iV hiU
            dU dV x (iU a)] at h
        refine ⟨a, h, ?_⟩
        rw [hdV.diag]
        exact (hpos j hj.1).le
      · have hxOutside : ∀ a : A, x ≠ iU a := by
          intro a ha
          exact hx ⟨a, ha.symm⟩
        have hzOutside : ∀ a : A, z ≠ iV a := by
          intro a ha
          exact hz ⟨a, ha.symm⟩
        let x0 : MetricOutsideRoot iU := ⟨x, hxOutside⟩
        let z0 : MetricOutsideRoot iV := ⟨z, hzOutside⟩
        have hL : metricRootedLeft iU iV hiU x =
            (.inr (.inl x0) : MetricRootedAmalgamVertex iU iV) :=
          metricRootedLeft_outside iU iV hiU x0
        have hR : metricRootedRight iU iV hiV z =
            (.inr (.inr z0) : MetricRootedAmalgamVertex iU iV) :=
          metricRootedRight_outside iU iV hiV z0
        rw [hL, hR] at h
        change finiteMetricBaseCrossDistance S dU dV iU iV x z ≤ j at h
        exact (finiteMetricBaseCrossDistance_le_jump_iff
          hpos hdU hdV iU iV x z hxOutside
          (fun a => (hzOutside a).symm) j hj).mp h
  · rintro ⟨a, hxa, haz⟩
    have hMetric : MetricOn S
        (metricRootedShortestDistance S iU iV dU dV) :=
      metricRootedShortestDistance_metric hpos hS hassoc
        iU iV hiU hiV hdU hdV hBase
    have hL : metricRootedShortestDistance S iU iV dU dV
        (metricRootedLeft iU iV hiU x)
        (.inl a) ≤ j := by
      rw [← metricRootedLeft_root iU iV hiU a,
        metricRootedShortestDistance_left_isometry S iU iV hiU
          dU dV x (iU a)]
      exact hxa
    have hR : metricRootedShortestDistance S iU iV dU dV
        (.inl a)
        (metricRootedRight iU iV hiV z) ≤ j := by
      rw [← metricRootedRight_root iU iV hiV a,
        metricRootedShortestDistance_right_isometry S iU iV hiV
          dU dV hBase (iV a) z]
      exact haz
    exact metric_jump_threshold_trans hpos hS hMetric (Or.inr hj)
      (metricRootedLeft iU iV hiU x) (.inl a)
      (metricRootedRight iU iV hiV z) hL hR

end AllThoseRamseyClasses.Applications.MetricSaturation
