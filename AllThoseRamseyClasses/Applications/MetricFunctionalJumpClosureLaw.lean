import AllThoseRamseyClasses.Applications.MetricJumpThresholds
import AllThoseRamseyClasses.Applications.MetricJumpSamedist

/-!
# Faithful per-jump closure law for the printed metric functional lift

The original 2019 class M_S^+ has, for each proper jump j,
one partial unary function F_j. Every j-equivalence class
has a unique designated LAST vertex c: F_j(c) is undefined;
for all other members y, F_j(y)=c and d(y,c)=j.

Express this literally as an Option-valued partial map. We
prove a useful exact consequence: any vertex x where F_j
is undefined must be the last vertex of its entire j-class,
and every different point in that class lies exactly distance
j from x. This is the axiom needed by the separate metric
amalgamation closure-last preservation lemmas.

This generic source-law formalization uses no amalgamation
and does not by itself validate the printed weak local
completion argument or the existence of the auxiliary lift.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Each j-class of a linearly ordered metric source has one
last closure vertex c. At the closure the partial function
is undefined; all other class members map to c and have
distance exactly j from it. -/
def MetricJumpClosureLaw
    {V : Type u} [LinearOrder V]
    (d : V → V → ℝ)
    (f : V → Option V)
    (j : ℝ) : Prop :=
  ∀ x : V, ∃ c : V,
    d x c ≤ j ∧
    f c = none ∧
    ∀ y : V, d y x ≤ j →
      y = c ∨ (y < c ∧ d y c = j ∧ f y = some c)

/-- Undefinedness of F_j identifies a genuine LAST closure vertex,
not an arbitrary hole in the partial-function graph. In particular
all other vertices j-equivalent to x must be at EXACT distance j. -/
theorem metricJumpClosureLaw_none_is_last
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ}
    (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (x : V) (hx : f x = none) :
    ∀ y : V, y ≠ x → d y x ≤ j →
      y < x ∧ d y x = j := by
  obtain ⟨c, _hxc, _hfc, hClass⟩ := hLaw x
  have hxx : d x x ≤ j := by
    rw [hd.diag x]
    exact (hpos j hj.1).le
  have hxcEq : x = c := by
    rcases hClass x hxx with h | ⟨_, _, hf⟩
    · exact h
    · rw [hx] at hf
      cases hf
  intro y hDifferent hyx
  rcases hClass y hyx with h | ⟨hlt, hExact, _⟩
  · exact False.elim (hDifferent (h.trans hxcEq.symm))
  · rw [← hxcEq] at hlt hExact
    exact ⟨hlt, hExact⟩

/-- If the same root partial function embeds into a side, an
undefined root value stays undefined in the side. This simple
exact induced-domain fact is essential: a root closure vertex
cannot silently become a nonclosure vertex of a larger side. -/
theorem rootClosure_none_preserved
    {A : Type u} {U : Type*}
    (i : A → U)
    (fA : A → Option A)
    (fU : U → Option U)
    (hExt : ∀ a : A,
      fU (i a) = Option.map i (fA a))
    (c : A) (hc : fA c = none) :
    fU (i c) = none := by
  rw [hExt c, hc]
  rfl

end AllThoseRamseyClasses.Applications.MetricSaturation
