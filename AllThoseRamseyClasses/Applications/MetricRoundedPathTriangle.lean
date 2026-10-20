import AllThoseRamseyClasses.Applications.MetricFourValues

/-!
# The rounded path-concatenation triangle inequality

A central nonempty-base metric amalgamation obligation is that
shortest rounded two-edge cross paths interact correctly with
genuine side-metric triangles. This file isolates the exact
scalar inequality used in that argument.

If x,a,b,c are allowed S-distances and x ≤ a+b, then
  x ⊕_S c ≤ a + (b ⊕_S c).
The conclusion is an ORDINARY real triangle inequality, not
merely an inequality in an abstract monoid. The proof uses the
actual real-supremum rounded sum, its monotonicity, associativity
on S, and the fact that a rounded sum never exceeds the
ordinary sum. All allowed S-values are explicitly recorded.

In particular, no unit 0 is inserted into S, no false
monotonicity on negative operands is assumed, and no strong
amalgamation claim is inferred from this scalar step alone.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The essential scalar triangle bound for extending a rounded
two-edge path across one genuine metric side edge. This is the
nontrivial rounding step in a shortest-path metric gluing
triangle.

The hypothesis x ≤ a+b is a real triangle condition. The
conclusion uses +, not an unsupported "rounded triangle"
relation, because it must ultimately prove the usual S-metric
triangle inequality after adjoining new cross distances. -/
theorem distanceSum_triangle_path_bound
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {x a b c : ℝ}
    (hx : x ∈ S) (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S)
    (htri : x ≤ a + b) :
    distanceSum S x c ≤ a + distanceSum S b c := by
  have hxb : x ≤ distanceSum S a b :=
    le_distanceSum_of_le_add hx htri
  calc
    distanceSum S x c =
        distanceSum S c x :=
      distanceSum_comm S x c
    _ ≤ distanceSum S c (distanceSum S a b) :=
      distanceSum_mono_right hc (hpos x hx).le hxb
    _ = distanceSum S (distanceSum S a b) c :=
      distanceSum_comm S c (distanceSum S a b)
    _ = distanceSum S a (distanceSum S b c) :=
      hassoc a ha b hb c hc
    _ ≤ a + distanceSum S b c :=
      distanceSum_le_add ha (hpos _ (hS b hb c hc)).le

/-- Mirrored scalar path inequality. The order of endpoints
does not matter because the genuine rounded sum is commutative. -/
theorem distanceSum_triangle_path_bound_right
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {x a b c : ℝ}
    (hx : x ∈ S) (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S)
    (htri : x ≤ a + b) :
    distanceSum S c x ≤ distanceSum S c b + a := by
  calc
    distanceSum S c x = distanceSum S x c :=
      distanceSum_comm S c x
    _ ≤ a + distanceSum S b c :=
      distanceSum_triangle_path_bound
        hpos hS hassoc hx ha hb hc htri
    _ = distanceSum S c b + a := by
      rw [distanceSum_comm S b c, add_comm]

end AllThoseRamseyClasses.Applications.MetricSaturation
