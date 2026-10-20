import AllThoseRamseyClasses.Applications.MetricRootedAmalgamDistance

/-!
# Exact old-side distances in the identified-base S-metric gluing

The vertex pushout and the finite rounded cross-distance table were
constructed separately. Here we verify that the ACTUAL distance table
restricts to the exact old metrics on both sides, not merely that the
old carrier maps are injective.

The right/root-root case requires agreement of the original metrics on
the common base. This assumption is essential: the table uses U's
root/root distances and V's right-side distances.

No triangle inequality is inferred. This result is the old-side
isometry component required before assembling the rooted metric
pushout, convex order, and completed partial functions.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- The full distance table restricts exactly to the U metric on the
disjoint root/off-root decomposition of U. -/
theorem metricRootedShortestDistance_leftSide
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (x y : A ⊕ MetricOutsideRoot iU) :
    metricRootedShortestDistance S iU iV dU dV
        (metricLeftSideIntoRooted iU iV x)
        (metricLeftSideIntoRooted iU iV y) =
      dU (metricSideEquiv iU hiU x) (metricSideEquiv iU hiU y) := by
  cases x with
  | inl a =>
      cases y with
      | inl b => rfl
      | inr y => rfl
  | inr x =>
      cases y with
      | inl b => rfl
      | inr y => rfl

/-- The right-side restriction is exact too, PROVIDED that the two
metrics agree on the shared base. This condition is needed precisely
for the root/root case. -/
theorem metricRootedShortestDistance_rightSide
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (x y : A ⊕ MetricOutsideRoot iV) :
    metricRootedShortestDistance S iU iV dU dV
        (metricRightSideIntoRooted iU iV x)
        (metricRightSideIntoRooted iU iV y) =
      dV (metricSideEquiv iV hiV x) (metricSideEquiv iV hiV y) := by
  cases x with
  | inl a =>
      cases y with
      | inl b => exact hBase a b
      | inr y => rfl
  | inr x =>
      cases y with
      | inl b => rfl
      | inr y => rfl

/-- The canonical inclusion of the original LEFT vertices preserves
their pairwise distance, including all diagonal/root pairs. -/
theorem metricRootedShortestDistance_left_isometry
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (x y : U) :
    metricRootedShortestDistance S iU iV dU dV
        (metricRootedLeft iU iV hiU x)
        (metricRootedLeft iU iV hiU y) = dU x y := by
  unfold metricRootedLeft
  rw [metricRootedShortestDistance_leftSide S iU iV hiU dU dV]
  simp

/-- The canonical inclusion of the original RIGHT vertices preserves
the whole V distance table, assuming exact agreement on the base. -/
theorem metricRootedShortestDistance_right_isometry
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (x y : V) :
    metricRootedShortestDistance S iU iV dU dV
        (metricRootedRight iU iV hiV x)
        (metricRootedRight iU iV hiV y) = dV x y := by
  unfold metricRootedRight
  rw [metricRootedShortestDistance_rightSide S iU iV hiV dU dV hBase]
  simp

end AllThoseRamseyClasses.Applications.MetricSaturation
