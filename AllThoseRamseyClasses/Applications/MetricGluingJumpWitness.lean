import AllThoseRamseyClasses.Applications.MetricJumpThresholds

/-!
# Jump-class crossing in shortest-path metric amalgamation

For a nonempty metric amalgamation base A, the cross-side distance
is the *minimum* of the rounded sums p(a) ⊕ q(a) over common
vertices a ∈ A. At a proper jump j, the cross distance is ≤ j if
and only if some common vertex lies within j of **both** endpoints.

This is the exact scalar lemma needed to show that a j-equivalence
class crossing the two sides of a metric amalgam has a witness in
the common base. It does NOT assume a class-level strong amalgam:
the abstract minimum and attainment hypotheses below are explicit.

When A is empty, no witness can be chosen; cross distances must be
defined separately, at the maximum S, which is NOT a proper jump
(the paper's Jump definition requires a strictly larger distance).
The exception is a separate step in the class-level construction.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Witness criterion for threshold crossing in a rounded-sum
minimum. The candidate set may be indexed by any type, not only a
finite carrier; attainment and the lower-bound property are stated
precisely and separately.

The forward implication does not depend on the equality of a
source and target class maximum. The reverse implication uses the
actual idempotence distanceSum j j = j from the *proper* jump. -/
theorem minimum_distanceSum_le_jump_iff_witness {S : Set ℝ}
    {A : Type u} (hpos : Positive S)
    (p q : A → ℝ) (hp : ∀ a, p a ∈ S) (hq : ∀ a, q a ∈ S)
    (j d : ℝ) (hj : Jump S j)
    (hLower : ∀ a : A, d ≤ distanceSum S (p a) (q a))
    (hAttain : ∃ a : A, d = distanceSum S (p a) (q a)) :
    d ≤ j ↔ ∃ a : A, p a ≤ j ∧ q a ≤ j := by
  constructor
  · intro hd
    obtain ⟨a, ha⟩ := hAttain
    have hs : distanceSum S (p a) (q a) ≤ j := by
      rw [← ha]
      exact hd
    have hpbound : p a ≤ distanceSum S (p a) (q a) :=
      left_le_distanceSum (hp a) (hpos (q a) (hq a)).le
    have hqbound : q a ≤ distanceSum S (p a) (q a) := by
      rw [distanceSum_comm S (p a) (q a)]
      exact left_le_distanceSum (hq a) (hpos (p a) (hp a)).le
    exact ⟨a, hpbound.trans hs, hqbound.trans hs⟩
  · rintro ⟨a, hpa, hqa⟩
    have hfirst : distanceSum S (p a) (q a) ≤
        distanceSum S (q a) j := by
      rw [distanceSum_comm S (p a) (q a)]
      exact distanceSum_mono_right (hq a)
        (hpos (p a) (hp a)).le hpa
    have hsecond : distanceSum S (q a) j ≤
        distanceSum S j j := by
      rw [distanceSum_comm S (q a) j]
      exact distanceSum_mono_right hj.1
        (hpos (q a) (hq a)).le hqa
    exact (hLower a).trans (hfirst.trans (hsecond.trans_eq hj.2.2))

end AllThoseRamseyClasses.Applications.MetricSaturation
