import AllThoseRamseyClasses.Applications.MetricFiniteNestedConvexOrder
import AllThoseRamseyClasses.Applications.MetricRootedAmalgamLinearOrder
import AllThoseRamseyClasses.Applications.MetricConvexityTransfer

/-!
# One simultaneously jump-convex order from compatible finite class keys

We isolate the final ORDER-ASSEMBLY step of metric strong
amalgamation: assume a finite nested list of class labels
on the already-defined identified-base metric carrier,
with each original side's labels monotone along its order,
and each proper S-jump represented by one exact label
whose equality detects precisely the jump-threshold distance.

Then there is a SINGLE linear order preserving both old
orders and convex at EVERY proper S-jump. No bound on
the number of proper jumps enters this abstract theorem.

The existence of the required exact class-label family for
the actual S-metric pushout is a separate geometric task,
currently being verified via the two-side key construction.
This theorem does NOT prove functional strong amalgamation,
the printed bounded nonmetric-cycle reduction or exact weak
local completion of arbitrary candidates.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w z

/-- Simultaneous convexity from an exact nested class-key list.
The *only* missing metric ingredient is the list of keys:
the order construction itself is fully determined here. -/
theorem metricRooted_allJumpConvexOrder_of_keys
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    {K : Type z}
    [Finite A] [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V] [LinearOrder K]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (hOrder : ∀ a b : A,
      iU a < iU b ↔ iV a < iV b)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (levels : List (MetricRootedAmalgamVertex iU iV → K))
    (hNested : NestedLevels levels)
    (hCover : ∀ j : ℝ, Jump S j →
      ∃ label ∈ levels,
        ∀ p q : MetricRootedAmalgamVertex iU iV,
          label p = label q ↔
            metricRootedShortestDistance S iU iV dU dV p q ≤ j)
    (hMonoLeft : ∀ label ∈ levels, ∀ x y : U, x < y →
      label (metricRootedLeft iU iV hiU x) ≤
        label (metricRootedLeft iU iV hiU y))
    (hMonoRight : ∀ label ∈ levels, ∀ x y : V, x < y →
      label (metricRootedRight iU iV hiV x) ≤
        label (metricRootedRight iU iV hiV y)) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiU x)
          (metricRootedLeft iU iV hiU y)) ∧
      (∀ x y : V, x < y →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiV x)
          (metricRootedRight iU iV hiV y)) ∧
      (@JumpConvex (MetricRootedAmalgamVertex iU iV) o S
        (metricRootedShortestDistance S iU iV dU dV)) := by
  classical
  obtain ⟨oldOrder, hOldL, hOldR⟩ :=
    metricRootedLinearOrder_exists iU iV hiU hiV hOrder
  let W := MetricRootedAmalgamVertex iU iV
  let newOrder : LinearOrder W := refineClassLevels oldOrder levels
  refine ⟨newOrder, ?_, ?_, ?_⟩
  · intro x y hxy
    apply refineClassLevels_preserves_comparison oldOrder levels
      (metricRootedLeft iU iV hiU x)
      (metricRootedLeft iU iV hiU y)
      (hOldL x y hxy)
    intro label hmem
    exact hMonoLeft label hmem x y hxy
  · intro x y hxy
    apply refineClassLevels_preserves_comparison oldOrder levels
      (metricRootedRight iU iV hiV x)
      (metricRootedRight iU iV hiV y)
      (hOldR x y hxy)
    intro label hmem
    exact hMonoRight label hmem x y hxy
  · change @JumpConvex W newOrder S
      (metricRootedShortestDistance S iU iV dU dV)
    intro j hj p q t hpq hqt hpt
    obtain ⟨label, hmem, hCharacter⟩ := hCover j hj
    have hLabels : label p = label t :=
      (hCharacter p t).mpr hpt
    have hConv : FibreConvex newOrder label :=
      refineClassLevels_all_convex oldOrder levels
        hNested label hmem
    have hpqKey : label p = label q :=
      hConv p q t hpq hqt hLabels
    have hqtKey : label q = label t :=
      hpqKey.symm.trans hLabels
    exact ⟨(hCharacter p q).mp hpqKey,
      (hCharacter q t).mp hqtKey⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
