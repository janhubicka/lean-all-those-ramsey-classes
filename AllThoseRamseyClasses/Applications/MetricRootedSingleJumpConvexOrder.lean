import AllThoseRamseyClasses.Applications.MetricRootedClassKeyGluing
import AllThoseRamseyClasses.Applications.MetricRootedAmalgamLinearOrder
import AllThoseRamseyClasses.Applications.MetricConvexOrderRefinement

/-!
# A genuinely jump-convex order on the finite rooted metric amalgam

The verified shortest-path amalgam possesses an ordinary common
linear order. The verified real metric jump-class key construction
gives monotone side keys agreeing exactly at shared classes.

Here we sort the WHOLE identified-base carrier by its glued
class key, using the ordinary common order only as a tie breaker.
The result keeps both original orders and is convex at the
specified proper jump j for the ACTUAL shortest-path metric.

This is the single-jump step, not yet a simultaneous order for all
jumps. That step will use the separate verified finite nested-
refinement theorem. We do not claim any auxiliary partial F_j
amalgamation or exact weak local-completion theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w z

/-- Under exact monotone compatible class keys, the identified-root
finite S-metric has a common original-order extension that is
genuinely convex at one chosen proper jump. -/
theorem metricRooted_oneJumpConvexOrder_exists
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    {K : Type z}
    [Finite A] [Nonempty A]
    [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V] [LinearOrder K]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (hOrderCompat : ∀ a b : A,
      iU a < iU b ↔ iV a < iV b)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (j : ℝ) (hj : Jump S j)
    (keyU : U → K) (keyV : V → K)
    (hMonoU : Monotone keyU) (hMonoV : Monotone keyV)
    (hRoot : ∀ a : A, keyU (iU a) = keyV (iV a))
    (hLeft : ∀ x y : U, keyU x = keyU y ↔ dU x y ≤ j)
    (hRight : ∀ x y : V, keyV x = keyV y ↔ dV x y ≤ j)
    (hCross : ∀ x : U, ∀ z : V,
      keyU x = keyV z ↔
        ∃ a : A, dU x (iU a) ≤ j ∧ dV (iV a) z ≤ j) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiU x)
          (metricRootedLeft iU iV hiU y)) ∧
      (∀ x y : V, x < y →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiV x)
          (metricRootedRight iU iV hiV y)) ∧
      (∀ p q t : MetricRootedAmalgamVertex iU iV,
        @LE.le _ o.toLE p q →
        @LE.le _ o.toLE q t →
        metricRootedShortestDistance S iU iV dU dV p t ≤ j →
          metricRootedShortestDistance S iU iV dU dV p q ≤ j ∧
          metricRootedShortestDistance S iU iV dU dV q t ≤ j) := by
  classical
  obtain ⟨o0, hOrdU, hOrdV⟩ :=
    metricRootedLinearOrder_exists iU iV hiU hiV hOrderCompat
  let W := MetricRootedAmalgamVertex iU iV
  let label : W → K :=
    metricRootedClassKey iU iV keyU keyV
  let o : LinearOrder W := @labelFirstOrder W K o0 _ label
  have hEq : ∀ p q : W, label p = label q ↔
      metricRootedShortestDistance S iU iV dU dV p q ≤ j :=
    metricRootedClassKey_eq_iff_distance hpos hS hassoc
      iU iV hiU hiV hdU hdV hBase j hj
      keyU keyV hRoot hLeft hRight hCross
  refine ⟨o, ?_, ?_, ?_⟩
  · intro x y hxy
    have hKey :
        label (metricRootedLeft iU iV hiU x) ≤
        label (metricRootedLeft iU iV hiU y) := by
      change metricRootedClassKey iU iV keyU keyV
        (metricRootedLeft iU iV hiU x) ≤
        metricRootedClassKey iU iV keyU keyV
          (metricRootedLeft iU iV hiU y)
      rw [metricRootedClassKey_left iU iV hiU keyU keyV x,
          metricRootedClassKey_left iU iV hiU keyU keyV y]
      exact hMonoU (le_of_lt hxy)
    exact @labelFirst_strict_of_label_mono W K o0 _
      label _ _ (hOrdU x y hxy) hKey
  · intro x y hxy
    have hKey :
        label (metricRootedRight iU iV hiV x) ≤
        label (metricRootedRight iU iV hiV y) := by
      change metricRootedClassKey iU iV keyU keyV
        (metricRootedRight iU iV hiV x) ≤
        metricRootedClassKey iU iV keyU keyV
          (metricRootedRight iU iV hiV y)
      rw [metricRootedClassKey_right iU iV hiV keyU keyV hRoot x,
          metricRootedClassKey_right iU iV hiV keyU keyV hRoot y]
      exact hMonoV (le_of_lt hxy)
    exact @labelFirst_strict_of_label_mono W K o0 _
      label _ _ (hOrdV x y hxy) hKey
  · intro p q t hpq hqt hpt
    have hLabels : label p = label t := (hEq p t).mpr hpt
    have hPQ : label p = label q :=
      @labelFirst_fibre_convex W K o0 _ label
        p q t hpq hqt hLabels
    have hQT : label q = label t :=
      hPQ.symm.trans hLabels
    exact ⟨(hEq p q).mp hPQ, (hEq q t).mp hQT⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
