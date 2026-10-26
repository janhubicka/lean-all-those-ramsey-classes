import AllThoseRamseyClasses.Applications.MetricFourValues
import Mathlib.Tactic

/-!
# Adversarial audit of the printed nonmetric-cycle compression bound

The 2019 lemma `lem:Sequivalence` claims that any non-S-metric
cycle can be compressed to one with at most |S| vertices, while
its proof explicitly insists that the resulting cycle has at
least THREE vertices (including a special triangle case).

The allowed two-distance set S={1,3} satisfies the actual
four-values condition. Nevertheless the 3-cycle with edge
lengths (1,1,3) is nonmetric, since 3 > 1+1.

Thus the *literal bound* |S|=2 cannot be correct for this
case. This audit does NOT formalize the general path-collapse
lemma, nor does it refute the Ramsey theorem; it certifies
the concrete arithmetic and four-values input needed for
an independent paper referee correction.

A candidate correction is to replace |S| by max(3,|S|)
in the cycle reduction lemma, then audit the last replacement
claim and the downstream numerical local completion cutoff.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The allowed positive two-distance set {1,3} genuinely
satisfies the same four-values condition as in the paper. -/
theorem one_three_fourValues :
    FourValues ({(1 : ℝ), 3} : Set ℝ) := by
  intro a ha b hb c hc d hd hex
  obtain ⟨x, hx, hax, hcx⟩ := hex
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd hx
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;>
    rcases hx with rfl | rfl
  all_goals
    first
    | exact ⟨1, by simp, by norm_num [Triangle], by norm_num [Triangle]⟩
    | exact ⟨3, by simp, by norm_num [Triangle], by norm_num [Triangle]⟩
    | norm_num [Triangle] at hax
    | norm_num [Triangle] at hcx

/-- The actual triangle of edge lengths (1,1,3) is not a
real metric triangle, even though all three edge lengths
belong to the four-values set {1,3}. -/
theorem one_three_nonmetric_triangle :
    ¬ Triangle (1 : ℝ) 1 3 := by
  norm_num [Triangle]

/-- The upper bound |S| in the literal printed lemma would
demand a cycle of at most 2 vertices, contradicting its
own minimum cycle length 3. -/
theorem one_three_cardinality_less_than_triangle :
    (({(1 : ℝ), 3} : Finset ℝ).card) < 3 := by
  norm_num

end AllThoseRamseyClasses.Applications.MetricSaturation
