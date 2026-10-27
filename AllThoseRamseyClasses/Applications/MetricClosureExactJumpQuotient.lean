import AllThoseRamseyClasses.Applications.MetricLocalClosureCoherence

/-!
# The designated F_j closure is the exact proper-jump quotient

The printed finite metric auxiliary lift names each j-class
by its unique final F_j closure vertex. This module makes
that statement exact in the original Option-valued language,
without introducing a new quotient or choosing arbitrary
representatives.

For every genuine S-metric and every proper jump j whose
partial function satisfies the FULL printed class law:
  (1) x lies within j of its F_j closure representative;
  (2) the representatives of x and y are equal exactly
      when d(x,y) <= j.
The reverse direction is not merely F_j invariance: it
uses the proved idempotent j-threshold transitivity.

This is useful in the local-completion proof: local tests
can force equality of closure targets along a short path,
and one final local test at its endpoints can then certify
the desired j-equivalence or yield a nonmetric-cycle
obstruction. The original weak-substructure quantifiers
and numerical cutoff remain separate and unverified.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Each original vertex lies within the proper jump
radius of the designated closure point determined by
its literal Option-valued partial function. -/
theorem metricClosureRepresentative_close_to_source
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (x : V) :
    d x (metricClosureRepresentative f x) ≤ j := by
  obtain ⟨c, hxc, hcNone, hClass⟩ := hLaw x
  have hxx : d x x ≤ j := by
    rw [hd.diag x]
    exact (hpos j hj.1).le
  rcases hClass x hxx with heq | ⟨_, _, hfx⟩
  · subst x
    simp only [metricClosureRepresentative, hcNone,
      Option.getD_none]
    rw [hd.diag]
    exact (hpos j hj.1).le
  · have hRepresentative : metricClosureRepresentative f x = c := by
      simp [metricClosureRepresentative, hfx]
    rw [hRepresentative]
    exact hxc

/-- EXACT class-quotient semantics of the printed F_j maps.
Equality of partial-function closure representatives is
equivalent to the actual metric j-threshold relation. -/
theorem metricClosureRepresentative_eq_iff_jump_close
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (x y : V) :
    metricClosureRepresentative f x =
        metricClosureRepresentative f y ↔
      d x y ≤ j := by
  constructor
  · intro heq
    have hx :=
      metricClosureRepresentative_close_to_source
        hpos hd j hj f hLaw x
    have hy :=
      metricClosureRepresentative_close_to_source
        hpos hd j hj f hLaw y
    rw [heq] at hx
    have hcy : d (metricClosureRepresentative f y) y ≤ j := by
      rw [hd.symm (metricClosureRepresentative f y) y]
      exact hy
    exact metric_jump_threshold_trans hpos hS hd (Or.inr hj)
      x (metricClosureRepresentative f y) y hx hcy
  · intro hxy
    exact metricClosureRepresentative_eq_of_close
      hpos hd j hj f hLaw x y hxy

end AllThoseRamseyClasses.Applications.MetricSaturation
