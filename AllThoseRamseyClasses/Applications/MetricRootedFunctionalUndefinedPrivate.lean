import AllThoseRamseyClasses.Applications.MetricRootedFunctionalUndefinedRoot
import AllThoseRamseyClasses.Applications.MetricRootedPrivateThresholdClass

/-!
# Private undefined metric closure points preserve every F_j value

If the source F_j is undefined at a private closure vertex c
outside the induced closed root, the entire j-class of c avoids
the root. This is a formal consequence of the source F_j law
and the induced partial-function restriction (not an assumption
about the shape of the metric amalgam).

The verified exact private-class decomposition therefore shows
that every point in the glued j-class of c is already in its
original source side. The original F_j class law transfers its
value, last-point order and exact distance to the merged carrier.

Both LEFT-private and RIGHT-private cases are proven. Together
with the separately verified shared-root case, these will
supply the second pointwise property needed to recover the
whole functional class law of the printed auxiliary lift.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- An undefined LEFT-private F_j closure remains the
designated last target of every different member of its
whole glued j-class, including exact option-valued F_j. -/
theorem metricRootedPartialFunction_none_leftPrivate_target
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A] [LinearOrder U]
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
    (fA : A → Option A)
    (fU : U → Option U) (fV : V → Option V)
    (hExtU : ∀ a : A,
      fU (iU a) = Option.map iU (fA a))
    (hLawU : MetricJumpClosureLaw dU fU j)
    (x : MetricOutsideRoot iU)
    (hNone :
      metricRootedPartialFunction iU iV hiU hiV fU fV
        (.inr (.inl x)) = none)
    (p : MetricRootedAmalgamVertex iU iV)
    (hDifferent : p ≠ .inr (.inl x))
    (hClose : metricRootedShortestDistance S iU iV dU dV
      p (.inr (.inl x)) ≤ j) :
    @LT.lt _ o.toLT p (.inr (.inl x)) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (.inr (.inl x)) = j ∧
      metricRootedPartialFunction iU iV hiU hiV fU fV
        p = some (.inr (.inl x)) := by
  have hXMap :
      metricRootedLeft iU iV hiU x.val =
        (.inr (.inl x) : MetricRootedAmalgamVertex iU iV) := by
    unfold metricRootedLeft
    rw [← metricSideEquiv_inr iU hiU x,
      (metricSideEquiv iU hiU).symm_apply_apply]
    rfl
  have hUNone : fU x.val = none := by
    change Option.map (metricRootedLeft iU iV hiU)
      (fU x.val) = none at hNone
    cases hf : fU x.val with
    | none => simpa [hf]
    | some v => simp [hf] at hNone
  have hNoRoot : ∀ a : A, ¬ dU x.val (iU a) ≤ j :=
    metricPrivateClosure_disjoint_from_closed_root
      hpos hdU j hj iU fA fU hExtU hLawU
      x.val hUNone x.property
  have hPrivate :=
    metricRooted_privateLeftThresholdClass_eq
      hpos hS hassoc iU iV hiU hiV
      hdU hdV hBase j hj x.val hNoRoot
  have hpMember :
      p ∈ metricRootedLeft iU iV hiU ''
        {y : U | dU y x.val ≤ j} := by
    rw [← hPrivate]
    change metricRootedShortestDistance S iU iV dU dV
      p (metricRootedLeft iU iV hiU x.val) ≤ j
    rw [hXMap]
    exact hClose
  obtain ⟨y, hyClose, hMap⟩ := hpMember
  have hYDifferent : y ≠ x.val := by
    intro hy
    have hp : p = (.inr (.inl x) :
        MetricRootedAmalgamVertex iU iV) := by
      calc
        p = metricRootedLeft iU iV hiU y := hMap.symm
        _ = metricRootedLeft iU iV hiU x.val := by rw [hy]
        _ = .inr (.inl x) := hXMap
    exact hDifferent hp
  obtain ⟨hyBefore, hyDistance, hyValue⟩ :=
    metricJumpClosureLaw_none_is_exact_target
      hpos hdU j hj fU hLawU x.val hUNone
        y hYDifferent hyClose
  refine ⟨?_, ?_, ?_⟩
  · have h := hOrderU y x.val hyBefore
    rw [hMap, hXMap] at h
    exact h
  · rw [← hMap, ← hXMap,
      metricRootedShortestDistance_left_isometry
        S iU iV hiU dU dV y x.val]
    exact hyDistance
  · rw [← hMap, metricRootedPartialFunction_left
      iU iV hiU hiV fU fV y, hyValue]
    simpa using congrArg Option.some hXMap

/-- RIGHT-private counterpart, preserving the exact
function value, old order, and metric distance j.
The root-avoidance orientation is converted by symmetry. -/
theorem metricRootedPartialFunction_none_rightPrivate_target
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A] [LinearOrder V]
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
    (fA : A → Option A)
    (fU : U → Option U) (fV : V → Option V)
    (hExtV : ∀ a : A,
      fV (iV a) = Option.map iV (fA a))
    (hRoot : ∀ a : A,
      Option.map (metricRootedLeft iU iV hiU) (fU (iU a)) =
        Option.map (metricRootedRight iU iV hiV) (fV (iV a)))
    (hLawV : MetricJumpClosureLaw dV fV j)
    (z : MetricOutsideRoot iV)
    (hNone :
      metricRootedPartialFunction iU iV hiU hiV fU fV
        (.inr (.inr z)) = none)
    (p : MetricRootedAmalgamVertex iU iV)
    (hDifferent : p ≠ .inr (.inr z))
    (hClose : metricRootedShortestDistance S iU iV dU dV
      p (.inr (.inr z)) ≤ j) :
    @LT.lt _ o.toLT p (.inr (.inr z)) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (.inr (.inr z)) = j ∧
      metricRootedPartialFunction iU iV hiU hiV fU fV
        p = some (.inr (.inr z)) := by
  have hZMap :
      metricRootedRight iU iV hiV z.val =
        (.inr (.inr z) : MetricRootedAmalgamVertex iU iV) := by
    unfold metricRootedRight
    rw [← metricSideEquiv_inr iV hiV z,
      (metricSideEquiv iV hiV).symm_apply_apply]
    rfl
  have hVNone : fV z.val = none := by
    change Option.map (metricRootedRight iU iV hiV)
      (fV z.val) = none at hNone
    cases hf : fV z.val with
    | none => simpa [hf]
    | some v => simp [hf] at hNone
  have hNoRoot : ∀ a : A, ¬ dV z.val (iV a) ≤ j :=
    metricPrivateClosure_disjoint_from_closed_root
      hpos hdV j hj iV fA fV hExtV hLawV
      z.val hVNone z.property
  have hNoRootV : ∀ a : A, ¬ dV (iV a) z.val ≤ j := by
    intro a ha
    exact hNoRoot a (by
      rw [hdV.symm z.val (iV a)]
      exact ha)
  have hPrivate :=
    metricRooted_privateRightThresholdClass_eq
      hpos hS hassoc iU iV hiU hiV
      hdU hdV hBase j hj z.val hNoRootV
  have hpMember :
      p ∈ metricRootedRight iU iV hiV ''
        {y : V | dV y z.val ≤ j} := by
    rw [← hPrivate]
    change metricRootedShortestDistance S iU iV dU dV
      p (metricRootedRight iU iV hiV z.val) ≤ j
    rw [hZMap]
    exact hClose
  obtain ⟨y, hyClose, hMap⟩ := hpMember
  have hYDifferent : y ≠ z.val := by
    intro hy
    have hp : p = (.inr (.inr z) :
        MetricRootedAmalgamVertex iU iV) := by
      calc
        p = metricRootedRight iU iV hiV y := hMap.symm
        _ = metricRootedRight iU iV hiV z.val := by rw [hy]
        _ = .inr (.inr z) := hZMap
    exact hDifferent hp
  obtain ⟨hyBefore, hyDistance, hyValue⟩ :=
    metricJumpClosureLaw_none_is_exact_target
      hpos hdV j hj fV hLawV z.val hVNone
        y hYDifferent hyClose
  refine ⟨?_, ?_, ?_⟩
  · have h := hOrderV y z.val hyBefore
    rw [hMap, hZMap] at h
    exact h
  · rw [← hMap, ← hZMap,
      metricRootedShortestDistance_right_isometry
        S iU iV hiV dU dV hBase y z.val]
    exact hyDistance
  · rw [← hMap, metricRootedPartialFunction_right
      iU iV hiU hiV fU fV hRoot y, hyValue]
    simpa using congrArg Option.some hZMap

end AllThoseRamseyClasses.Applications.MetricSaturation
