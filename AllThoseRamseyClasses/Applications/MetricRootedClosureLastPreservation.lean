import AllThoseRamseyClasses.Applications.MetricRootedPrivateThresholdClass
import AllThoseRamseyClasses.Applications.MetricRootedSharedThresholdClass
import AllThoseRamseyClasses.Applications.MetricRootedAmalgamLinearOrder

/-!
# Preserve the designated last closure vertex in metric strong amalgamation

The printed functional lift M_S^+ requires the designated last
vertex of every proper-jump class to lie at distance EXACTLY j from
each other vertex of its class. The existence of a compatible
jump-convex order alone is not enough to certify this condition.

These separate theorems show that the closure vertex and exact-j
condition persist across the verified identified-root S-metric
amalgam provided they already hold on BOTH source sides:

* shared classes: a common root vertex a is the last, exact-j
  closure point on each original side; any common side-order
  extension keeps it last and at distance exactly j;
* private classes: if a proper-jump class avoids the root,
  the exact class-decomposition theorem puts it entirely
  on its original side, so its old last vertex and exact-j
  distances are unchanged.

This is not the full functional strong-amalgamation theorem:
one must still glue the partial maps F_j, verify their induced
restriction/root compatibility, and check every designated
class simultaneously. The bounded nonmetric-cycle and exact
weak local-completion argument of the printed paper remains
a distinct obligation.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- A COMMON ROOT closure representative stays last and at
distance j from every different member of its glued class,
provided the same exact requirement holds on both sides. -/
theorem metricRooted_sharedClosureVertex_preserved
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
    (hOrderU : ∀ x y : U, x < y →
      @LT.lt _ o.toLT
        (metricRootedLeft iU iV hiU x)
        (metricRootedLeft iU iV hiU y))
    (hOrderV : ∀ x y : V, x < y →
      @LT.lt _ o.toLT
        (metricRootedRight iU iV hiV x)
        (metricRootedRight iU iV hiV y))
    (a : A) (j : ℝ)
    (hClosureU : ∀ x : U, x ≠ iU a →
      dU x (iU a) ≤ j →
        x < iU a ∧ dU x (iU a) = j)
    (hClosureV : ∀ z : V, z ≠ iV a →
      dV z (iV a) ≤ j →
        z < iV a ∧ dV z (iV a) = j)
    (p : MetricRootedAmalgamVertex iU iV)
    (hpClose :
      metricRootedShortestDistance S iU iV dU dV p (.inl a) ≤ j)
    (hpDifferent : p ≠ .inl a) :
    (@LT.lt _ o.toLT p (.inl a)) ∧
      metricRootedShortestDistance S iU iV dU dV p (.inl a) = j := by
  rcases metricRooted_covers iU iV hiU hiV p with
    ⟨x, hx⟩ | ⟨z, hz⟩
  · have hxDifferent : x ≠ iU a := by
      intro heq
      rw [heq, metricRootedLeft_root] at hx
      exact hpDifferent hx.symm
    have hxClose : dU x (iU a) ≤ j := by
      have h := hpClose
      rw [← hx, ← metricRootedLeft_root iU iV hiU a,
        metricRootedShortestDistance_left_isometry S iU iV
          hiU dU dV x (iU a)] at h
      exact h
    obtain ⟨hxBefore, hxDistance⟩ :=
      hClosureU x hxDifferent hxClose
    have hBefore := hOrderU x (iU a) hxBefore
    rw [hx, metricRootedLeft_root] at hBefore
    refine ⟨hBefore, ?_⟩
    rw [← hx, ← metricRootedLeft_root iU iV hiU a,
      metricRootedShortestDistance_left_isometry
        S iU iV hiU dU dV x (iU a)]
    exact hxDistance
  · have hzDifferent : z ≠ iV a := by
      intro heq
      rw [heq, metricRootedRight_root] at hz
      exact hpDifferent hz.symm
    have hzClose : dV z (iV a) ≤ j := by
      have h := hpClose
      rw [← hz, ← metricRootedRight_root iU iV hiV a,
        metricRootedShortestDistance_right_isometry
          S iU iV hiV dU dV hBase z (iV a)] at h
      exact h
    obtain ⟨hzBefore, hzDistance⟩ :=
      hClosureV z hzDifferent hzClose
    have hBefore := hOrderV z (iV a) hzBefore
    rw [hz, metricRootedRight_root] at hBefore
    refine ⟨hBefore, ?_⟩
    rw [← hz, ← metricRootedRight_root iU iV hiV a,
      metricRootedShortestDistance_right_isometry
        S iU iV hiV dU dV hBase z (iV a)]
    exact hzDistance

/-- A left-private proper-jump closure point stays last
in its actual whole glued jump class, with all old j-distances
exact. No new right-side vertex enters this class. -/
theorem metricRooted_privateLeftClosureVertex_preserved
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder U]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
    (hOrderU : ∀ x y : U, x < y →
      @LT.lt _ o.toLT
        (metricRootedLeft iU iV hiU x)
        (metricRootedLeft iU iV hiU y))
    (j : ℝ) (hj : Jump S j)
    (x : U)
    (hNoRoot : ∀ a : A, ¬ dU x (iU a) ≤ j)
    (hClosureU : ∀ y : U, y ≠ x → dU y x ≤ j →
      y < x ∧ dU y x = j)
    (p : MetricRootedAmalgamVertex iU iV)
    (hpClose :
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedLeft iU iV hiU x) ≤ j)
    (hpDifferent : p ≠ metricRootedLeft iU iV hiU x) :
    (@LT.lt _ o.toLT p (metricRootedLeft iU iV hiU x)) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedLeft iU iV hiU x) = j := by
  have hPrivate := metricRooted_privateLeftThresholdClass_eq
    hpos hS hassoc iU iV hiU hiV
    hdU hdV hBase j hj x hNoRoot
  have hMembership :
      p ∈ metricRootedLeft iU iV hiU ''
        {y : U | dU y x ≤ j} := by
    rw [← hPrivate]
    exact hpClose
  obtain ⟨y, hy, hMap⟩ := hMembership
  have hyDifferent : y ≠ x := by
    intro heq
    rw [heq] at hMap
    exact hpDifferent hMap.symm
  obtain ⟨hyBefore, hyDistance⟩ :=
    hClosureU y hyDifferent hy
  have hBefore := hOrderU y x hyBefore
  rw [hMap] at hBefore
  refine ⟨hBefore, ?_⟩
  rw [← hMap,
    metricRootedShortestDistance_left_isometry
      S iU iV hiU dU dV y x]
  exact hyDistance

/-- The symmetric private-right closure point is preserved. -/
theorem metricRooted_privateRightClosureVertex_preserved
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
    (hOrderV : ∀ x y : V, x < y →
      @LT.lt _ o.toLT
        (metricRootedRight iU iV hiV x)
        (metricRootedRight iU iV hiV y))
    (j : ℝ) (hj : Jump S j)
    (z : V)
    (hNoRoot : ∀ a : A, ¬ dV (iV a) z ≤ j)
    (hClosureV : ∀ y : V, y ≠ z → dV y z ≤ j →
      y < z ∧ dV y z = j)
    (p : MetricRootedAmalgamVertex iU iV)
    (hpClose :
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedRight iU iV hiV z) ≤ j)
    (hpDifferent : p ≠ metricRootedRight iU iV hiV z) :
    (@LT.lt _ o.toLT p (metricRootedRight iU iV hiV z)) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedRight iU iV hiV z) = j := by
  have hPrivate := metricRooted_privateRightThresholdClass_eq
    hpos hS hassoc iU iV hiU hiV
    hdU hdV hBase j hj z hNoRoot
  have hMembership :
      p ∈ metricRootedRight iU iV hiV ''
        {y : V | dV y z ≤ j} := by
    rw [← hPrivate]
    exact hpClose
  obtain ⟨y, hy, hMap⟩ := hMembership
  have hyDifferent : y ≠ z := by
    intro heq
    rw [heq] at hMap
    exact hpDifferent hMap.symm
  obtain ⟨hyBefore, hyDistance⟩ :=
    hClosureV y hyDifferent hy
  have hBefore := hOrderV y z hyBefore
  rw [hMap] at hBefore
  refine ⟨hBefore, ?_⟩
  rw [← hMap,
    metricRootedShortestDistance_right_isometry
      S iU iV hiV dU dV hBase y z]
  exact hyDistance

end AllThoseRamseyClasses.Applications.MetricSaturation
