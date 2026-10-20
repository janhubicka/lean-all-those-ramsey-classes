import AllThoseRamseyClasses.Applications.MetricRootedAmalgamSideIsometries

/-!
# Exact jump-class intersection of the identified rooted S-metric pushout

For any real threshold j, the set of glued vertices within j of a
COMMON BASE vertex a is exactly the union of the corresponding
sets from the two original sides, using their actual injective
rooted carrier embeddings.

This identity uses neither a guessed cross distance nor an
unproved ordering lemma. The proof covers every vertex by one
of the two original sides, and then applies exact old-side
isometries and literal identification of root points.

At a proper jump, it describes the complete shared j-class
as the union of the two corresponding side j-classes. It is
one ingredient for recursive construction of convex amalgam
orders; classes which do not touch the root require a separate
root-witness argument.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- The identified-root union is covered by the TWO original side
images, including each root vertex only once. This is independent
of the distance function and order. -/
private theorem metricRooted_covers
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    (p : MetricRootedAmalgamVertex iU iV) :
    (∃ x : U, metricRootedLeft iU iV hiU x = p) ∨
      (∃ z : V, metricRootedRight iU iV hiV z = p) := by
  cases p with
  | inl a =>
      exact Or.inl ⟨iU a, metricRootedLeft_root iU iV hiU a⟩
  | inr p =>
      cases p with
      | inl x =>
          refine Or.inl ⟨x.val, ?_⟩
          unfold metricRootedLeft
          rw [← metricSideEquiv_inr iU hiU x,
            (metricSideEquiv iU hiU).symm_apply_apply]
          rfl
      | inr z =>
          refine Or.inr ⟨z.val, ?_⟩
          unfold metricRootedRight
          rw [← metricSideEquiv_inr iV hiV z,
            (metricSideEquiv iV hiV).symm_apply_apply]
          rfl

/-- For each original root point a, the ENTIRE j-threshold class
in the genuine common-root carrier is exactly the union of the
original j-threshold classes from both metric sides. The equality
holds at any real cutoff j, not only at a proper jump. -/
theorem metricRooted_rootThresholdClass_eq_union
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (a : A) (j : ℝ) :
    {p : MetricRootedAmalgamVertex iU iV |
       metricRootedShortestDistance S iU iV dU dV p (.inl a) ≤ j} =
      (metricRootedLeft iU iV hiU ''
        {x : U | dU x (iU a) ≤ j}) ∪
      (metricRootedRight iU iV hiV ''
        {z : V | dV z (iV a) ≤ j}) := by
  ext p
  constructor
  · intro hp
    change metricRootedShortestDistance S iU iV dU dV
      p (.inl a) ≤ j at hp
    rcases metricRooted_covers iU iV hiU hiV p with
      ⟨x, hx⟩ | ⟨z, hz⟩
    · have hDist := hp
      rw [← hx, ← metricRootedLeft_root iU iV hiU a,
        metricRootedShortestDistance_left_isometry S iU iV hiU
          dU dV x (iU a)] at hDist
      exact Or.inl ⟨x, hDist, hx⟩
    · have hDist := hp
      rw [← hz, ← metricRootedRight_root iU iV hiV a,
        metricRootedShortestDistance_right_isometry S iU iV hiV
          dU dV hBase z (iV a)] at hDist
      exact Or.inr ⟨z, hDist, hz⟩
  · intro hp
    rcases hp with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
    · change metricRootedShortestDistance S iU iV dU dV
        (metricRootedLeft iU iV hiU x) (.inl a) ≤ j
      rw [← metricRootedLeft_root iU iV hiU a,
        metricRootedShortestDistance_left_isometry S iU iV hiU
          dU dV x (iU a)]
      exact hx
    · change metricRootedShortestDistance S iU iV dU dV
        (metricRootedRight iU iV hiV z) (.inl a) ≤ j
      rw [← metricRootedRight_root iU iV hiV a,
        metricRootedShortestDistance_right_isometry S iU iV hiV
          dU dV hBase z (iV a)]
      exact hz

end AllThoseRamseyClasses.Applications.MetricSaturation
