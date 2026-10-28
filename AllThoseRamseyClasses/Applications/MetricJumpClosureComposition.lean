import AllThoseRamseyClasses.Applications.MetricFunctionalJumpClosureLaw

/-!
# Two-step closure functions collapse to the higher direct closure

A finite metric functional expansion has one Option-valued F_j for
each proper jump j. The printed class law makes each defined F_j
arrow point to the unique last vertex of its j-class.

The following algebraic normal form is an important source-closure
estimate. Whenever

  F_j(x) = some y    and    F_k(y) = some z,

the proper jump k must be STRICTLY above j, and F_k(x)=some z.
Consequently an iterated defined F-chain never produces a vertex
that cannot already be reached by one of the F_k from its start.

This is proved only for a VALID metric target satisfying the full
proper-jump closure law. The original local-completion proof still
must transfer these identities back to weak candidate subsets
and account for U-closed support tests and the printed numerical
cutoff. This file makes no unjustified claim about those candidates.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A defined F_j edge goes strictly forward to the designated
last j-class vertex, at distance EXACTLY j, where F_j becomes
undefined. In particular it is never a loop. -/
theorem metricJumpClosureLaw_some_goes_to_last
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (x y : V) (hxy : f x = some y) :
    x < y ∧ d x y = j ∧ f y = none := by
  obtain ⟨c, _hxc, hcNone, hClass⟩ := hLaw x
  have hxx : d x x ≤ j := by
    rw [hd.diag x]
    exact (hpos j hj.1).le
  rcases hClass x hxx with hx | ⟨hlt, hdist, hfx⟩
  · subst c
    rw [hcNone] at hxy
    cases hxy
  · have hc_eq_y : c = y :=
      Option.some.inj (hfx.symm.trans hxy)
    subst y
    exact ⟨hlt, hdist, hcNone⟩

/-- Complete two-step F_j composition normalization on any
valid metric-functional expansion. The jump levels MUST rise
strictly along defined arrows, and their composed target is
already the direct higher-jump target of the start vertex.

No finiteness of S and no choices of representative are needed. -/
theorem metricJumpClosureLaw_defined_composition_normalform
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (f : ℝ → V → Option V)
    (hLaw : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw d (f j) j)
    (j k : ℝ) (hj : Jump S j) (hk : Jump S k)
    (x y z : V)
    (hxy : f j x = some y)
    (hyz : f k y = some z) :
    j < k ∧ f k x = some z := by
  obtain ⟨hxylt, hxyDist, hfyNone⟩ :=
    metricJumpClosureLaw_some_goes_to_last
      hpos hd j hj (f j) (hLaw j hj) x y hxy
  obtain ⟨hyzlt, hyzDist, _⟩ :=
    metricJumpClosureLaw_some_goes_to_last
      hpos hd k hk (f k) (hLaw k hk) y z hyz
  have hjk : j < k := by
    by_contra hn
    have hkj : k ≤ j := le_of_not_gt hn
    have hClose : d z y ≤ j := by
      rw [hd.symm z y, hyzDist]
      exact hkj
    have hzBefore : z < y :=
      (metricJumpClosureLaw_none_is_last
        hpos hd j hj (f j) (hLaw j hj)
        y hfyNone z (ne_of_gt hyzlt) hClose).1
    exact (not_lt_of_ge (le_of_lt hyzlt)) hzBefore
  have hCloseXY : d x y ≤ k := by
    rw [hxyDist]
    exact le_of_lt hjk
  obtain ⟨c, _hyc, hcNone, hClass⟩ := hLaw k hk y
  have hyy : d y y ≤ k := by
    rw [hd.diag y]
    exact (hpos k hk.1).le
  have hcEqZ : c = z := by
    rcases hClass y hyy with hyc | ⟨_, _, hfyc⟩
    · subst c
      rw [hcNone] at hyz
      cases hyz
    · exact Option.some.inj (hfyc.symm.trans hyz)
  subst z
  rcases hClass x hCloseXY with hxc | ⟨_, _, hfxc⟩
  · have hxlty : x < y := hxylt
    have hyltc : y < c := hyzlt
    exact False.elim ((ne_of_lt (lt_trans hxlty hyltc)) hxc)
  · exact ⟨hjk, hfxc⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
