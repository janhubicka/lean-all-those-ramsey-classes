import AllThoseRamseyClasses.Applications.MetricRealRootClassKeys
import AllThoseRamseyClasses.Applications.MetricRootedJumpRootWitness
import AllThoseRamseyClasses.Applications.MetricRootedSharedThresholdClass

/-!
# Exact finite-root class keys on the ACTUAL glued metric carrier

A pair of side-class keys for two convexly ordered S-metrics,
compatible at every root point, induces one key on the genuine
identified-root metric pushout. We prove that this actual glued
key restricts EXACTLY to the two old side key maps.

At every proper jump j, when the side keys identify their
within-side j-classes and have the exact root-witness cross
criterion, equality of glued keys is equivalent to distance
at most j in the actual rounded shortest-path S-metric.

This is the bridge from algebraic shared/private class keys
to the actual S-metric jump-equivalence classes. It is not
yet a convex linear order, a functional amalgamation theorem,
or the printed weak local-completion argument.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w z

/-- The value at a common root is taken from the left key,
while off-root points use their own original side keys. -/
def metricRootedClassKey
    {A : Type u} {U : Type v} {V : Type w}
    {K : Type z}
    (iU : A → U) (iV : A → V)
    (keyU : U → K) (keyV : V → K) :
    MetricRootedAmalgamVertex iU iV → K
  | .inl a => keyU (iU a)
  | .inr (.inl x) => keyU x.val
  | .inr (.inr y) => keyV y.val

/-- The glued key restricts to the original left key
on the whole original left carrier, not only on root points. -/
theorem metricRootedClassKey_left
    {A : Type u} {U : Type v} {V : Type w}
    {K : Type z}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (keyU : U → K) (keyV : V → K)
    (x : U) :
    metricRootedClassKey iU iV keyU keyV
      (metricRootedLeft iU iV hiU x) = keyU x := by
  unfold metricRootedLeft
  generalize hp : (metricSideEquiv iU hiU).symm x = p
  have hOriginal : metricSideEquiv iU hiU p = x := by
    rw [← hp]
    exact (metricSideEquiv iU hiU).apply_symm_apply x
  cases p with
  | inl a =>
      change keyU (iU a) = keyU x
      rw [metricSideEquiv_inl] at hOriginal
      exact congrArg keyU hOriginal
  | inr y =>
      change keyU y.val = keyU x
      rw [metricSideEquiv_inr] at hOriginal
      exact congrArg keyU hOriginal

/-- The glued key restricts to the original right key;
agreement on EVERY shared root vertex is indispensable. -/
theorem metricRootedClassKey_right
    {A : Type u} {U : Type v} {V : Type w}
    {K : Type z}
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (keyU : U → K) (keyV : V → K)
    (hRoot : ∀ a : A, keyU (iU a) = keyV (iV a))
    (z : V) :
    metricRootedClassKey iU iV keyU keyV
      (metricRootedRight iU iV hiV z) = keyV z := by
  unfold metricRootedRight
  generalize hp : (metricSideEquiv iV hiV).symm z = p
  have hOriginal : metricSideEquiv iV hiV p = z := by
    rw [← hp]
    exact (metricSideEquiv iV hiV).apply_symm_apply z
  cases p with
  | inl a =>
      change keyU (iU a) = keyV z
      rw [← hRoot a]
      rw [metricSideEquiv_inl] at hOriginal
      exact congrArg keyU hOriginal
  | inr y =>
      change keyV y.val = keyV z
      rw [metricSideEquiv_inr] at hOriginal
      exact congrArg keyV hOriginal

/-- One class key on the actual finite metric amalgam:
equality of the glued keys is exactly the genuine threshold
equivalence, for all four ordered combinations of source sides.
No phantom identifications of private classes occur. -/
theorem metricRootedClassKey_eq_iff_distance
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    {K : Type z}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (j : ℝ) (hj : Jump S j)
    (keyU : U → K) (keyV : V → K)
    (hRoot : ∀ a : A, keyU (iU a) = keyV (iV a))
    (hLeft : ∀ x y : U, keyU x = keyU y ↔ dU x y ≤ j)
    (hRight : ∀ x y : V, keyV x = keyV y ↔ dV x y ≤ j)
    (hCross : ∀ x : U, ∀ z : V,
      keyU x = keyV z ↔
        ∃ a : A, dU x (iU a) ≤ j ∧ dV (iV a) z ≤ j)
    (p q : MetricRootedAmalgamVertex iU iV) :
    metricRootedClassKey iU iV keyU keyV p =
        metricRootedClassKey iU iV keyU keyV q ↔
      metricRootedShortestDistance S iU iV dU dV p q ≤ j := by
  rcases metricRooted_covers iU iV hiU hiV p with
    ⟨x, rfl⟩ | ⟨z, rfl⟩
  · rcases metricRooted_covers iU iV hiU hiV q with
      ⟨y, rfl⟩ | ⟨t, rfl⟩
    · rw [metricRootedClassKey_left iU iV hiU keyU keyV x,
          metricRootedClassKey_left iU iV hiU keyU keyV y,
          metricRootedShortestDistance_left_isometry
            S iU iV hiU dU dV x y]
      exact hLeft x y
    · rw [metricRootedClassKey_left iU iV hiU keyU keyV x,
          metricRootedClassKey_right iU iV hiV keyU keyV hRoot t]
      exact (hCross x t).trans
        (metricRootedCross_le_jump_iff_root
          hpos hS hassoc iU iV hiU hiV hdU hdV
          hBase j hj x t).symm
  · rcases metricRooted_covers iU iV hiU hiV q with
      ⟨y, rfl⟩ | ⟨t, rfl⟩
    · rw [metricRootedClassKey_right iU iV hiV keyU keyV hRoot z,
          metricRootedClassKey_left iU iV hiU keyU keyV y]
      have hMetric : MetricOn S
          (metricRootedShortestDistance S iU iV dU dV) :=
        metricRootedShortestDistance_metric hpos hS hassoc
          iU iV hiU hiV hdU hdV hBase
      rw [eq_comm,
        hMetric.symm (metricRootedRight iU iV hiV z)
          (metricRootedLeft iU iV hiU y)]
      exact (hCross y z).trans
        (metricRootedCross_le_jump_iff_root
          hpos hS hassoc iU iV hiU hiV hdU hdV
          hBase j hj y z).symm
    · rw [metricRootedClassKey_right iU iV hiV keyU keyV hRoot z,
          metricRootedClassKey_right iU iV hiV keyU keyV hRoot t,
          metricRootedShortestDistance_right_isometry
            S iU iV hiV dU dV hBase z t]
      exact hRight z t

end AllThoseRamseyClasses.Applications.MetricSaturation
