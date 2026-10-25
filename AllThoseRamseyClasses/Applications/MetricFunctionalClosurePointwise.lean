import AllThoseRamseyClasses.Applications.MetricFunctionalJumpClosureLaw

/-!
# Reconstruct the full metric F_j class law from pointwise properties

The original 2019 functional lift requires one closure point per
proper-jump class, last in its linear order, and F_j defined on
every other class member with exact edge length j.

It is enough to establish two genuinely local assertions:

* Every defined value F_j(x)=c targets an undefined last point c,
  with x<c and d(x,c)=j.
* Every undefined point c receives F_j(y)=c from every other
  j-close point y, which precedes c at exact distance j.

We prove that these two conditions imply the WHOLE original
classwise existence/every-member law. The only additional
metric ingredient is transitivity of the proper-jump threshold
relation, already kernel verified.

This makes the final proof that rooted partial function gluing
preserves the functional metric class law considerably shorter.
The conditions must of course be verified separately for the
actual glued F_j operations before applying this theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Entire 2019 j-class closure axiom follows from the two
pointwise properties, including their exact function domains.
This theorem assumes no finite carrier or artificial chosen
representatives. -/
theorem metricJumpClosureLaw_of_pointwise
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ}
    (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hDefined : ∀ x c : V,
      f x = some c → f c = none ∧ x < c ∧ d x c = j)
    (hUndefined : ∀ c : V,
      f c = none → ∀ y : V, y ≠ c →
        d y c ≤ j →
          y < c ∧ d y c = j ∧ f y = some c) :
    MetricJumpClosureLaw d f j := by
  intro x
  cases hf : f x with
  | none =>
      refine ⟨x, ?_, hf, ?_⟩
      · rw [hd.diag x]
        exact (hpos j hj.1).le
      · intro y hy
        by_cases hxy : y = x
        · exact Or.inl hxy
        · exact Or.inr (hUndefined x hf y hxy hy)
  | some c =>
      obtain ⟨hcNone, _, hxc⟩ := hDefined x c hf
      refine ⟨c, le_of_eq hxc, hcNone, ?_⟩
      intro y hyx
      by_cases hyc : y = c
      · exact Or.inl hyc
      · have hYC : d y c ≤ j :=
          metric_jump_threshold_trans hpos hS hd (Or.inr hj)
            y x c hyx (le_of_eq hxc)
        exact Or.inr (hUndefined c hcNone y hyc hYC)

end AllThoseRamseyClasses.Applications.MetricSaturation
