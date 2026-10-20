import AllThoseRamseyClasses.Applications.MetricFourValues

/-!
# A shortest rounded cross path and one base-side edge

The two-cross triangle controls distances between off-base points
on the same side. A different mixed triangle is needed when one
vertex of the three-point triangle belongs to the common metric
base:

  dU(x,iU a) ≤ δ(x,z) + dV(z,iV a).

If the shortest path for δ(x,z) goes through b rather than a,
the source left triangle passes from x to iU b to iU a.
The other side supplies the bridge from iV b through z to iV a.

This file isolates the *scalar* inequality required when a and b
are distinct (the base edge has a positive allowed S-distance):
  B ≤ A+E, E ≤ C+D  ⇒  B ≤ (A ⊕_S C)+D.
All operands in the rounded chain are genuinely in S, so
monotonicity and associativity of the paper's real-supremum
rounded operation apply. This is stronger than the raw real
path inequality B ≤ A+C+D, which alone would not control
intermediate rounding.

The same-base case has no positive E and must be treated
separately using the rounded sum's lower bound.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- From two genuine S-valued metric triangles across a positive
common-base edge, derive the ordinary real triangle bounded by
a rounded cross path and the final metric side edge. -/
theorem distanceSum_base_cross_triangle_bound
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {b a e c d : ℝ}
    (hb : b ∈ S) (ha : a ∈ S)
    (he : e ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hba : b ≤ a + e) (hecd : e ≤ c + d) :
    b ≤ distanceSum S a c + d := by
  calc
    b ≤ distanceSum S a e :=
      le_distanceSum_of_le_add hb hba
    _ ≤ distanceSum S a (distanceSum S c d) :=
      distanceSum_mono_right ha (hpos e he).le
        (le_distanceSum_of_le_add he hecd)
    _ = distanceSum S (distanceSum S a c) d :=
      (hassoc a ha c hc d hd).symm
    _ ≤ distanceSum S a c + d :=
      distanceSum_le_add (hS a ha c hc) (hpos d hd).le

end AllThoseRamseyClasses.Applications.MetricSaturation
