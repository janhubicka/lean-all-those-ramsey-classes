import AllThoseRamseyClasses.Applications.MetricFourValues

/-!
# Two-cross triangle bound for genuine rounded S-distances

This is the crucial scalar part of the missing triangle of the form
  d_U(x,y) ≤ δ(x,z) + δ(z,y)
in shortest-path amalgamation of S-metrics over a nonempty base.

The path x -- a -- b -- y in the first side gives the two metric
triangle inequalities
  t ≤ a + e,       x ≤ t + d.
The bridge between base vertices a,b is measured in the *other*
side by a two-edge path through z:
  e ≤ v + w.
All seven displayed positive lengths are REQUIRED to belong to S.
Using the actual rounded operation (the real supremum of allowed
distances below a+b), well-definedness, its monotonicity and
associativity, we prove

  x ≤ (a ⊕ v) + (w ⊕ d).

This is an ordinary REAL inequality. Merely bounding x by
a+v+w+d is NOT sufficient: rounding intermediate sums can
lose information. Associativity and membership in S are used
in the intermediate rounded triangles.

This handles the case of DISTINCT minimizing base points; the
same-base case is a direct triangle with no positive base edge.
No statement about the complete pushout metric is assumed.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Two nested genuine S-metric triangles, connected across a
second side through a common S-valued base edge, imply the
ordinary real two-cross-distance triangle after rounding.

The three inequalities are precisely the metric triangle
conditions needed in the eventual two-cross-distance amalgam:
x ≤ t+d, t ≤ a+e, and e ≤ v+w. -/
theorem distanceSum_twoCross_triangle_bound
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {x t a e d v w : ℝ}
    (hx : x ∈ S) (ht : t ∈ S) (ha : a ∈ S)
    (he : e ∈ S) (hd : d ∈ S)
    (hv : v ∈ S) (hw : w ∈ S)
    (hxt : x ≤ t + d)
    (hta : t ≤ a + e)
    (hev : e ≤ v + w) :
    x ≤ distanceSum S a v + distanceSum S w d := by
  have hxtRounded : x ≤ distanceSum S t d :=
    le_distanceSum_of_le_add hx hxt
  have htaRounded : t ≤ distanceSum S a e :=
    le_distanceSum_of_le_add ht hta
  have hevRounded : e ≤ distanceSum S v w :=
    le_distanceSum_of_le_add he hev
  have htaMonotone :
      distanceSum S t d ≤ distanceSum S (distanceSum S a e) d := by
    calc
      distanceSum S t d = distanceSum S d t :=
        distanceSum_comm S t d
      _ ≤ distanceSum S d (distanceSum S a e) :=
        distanceSum_mono_right hd (hpos t ht).le htaRounded
      _ = distanceSum S (distanceSum S a e) d :=
        distanceSum_comm S d _
  have hevMonotone :
      distanceSum S a e ≤ distanceSum S a (distanceSum S v w) :=
    distanceSum_mono_right ha (hpos e he).le hevRounded
  have hInner :
      distanceSum S (distanceSum S a e) d ≤
        distanceSum S (distanceSum S a (distanceSum S v w)) d := by
    calc
      distanceSum S (distanceSum S a e) d =
          distanceSum S d (distanceSum S a e) :=
        distanceSum_comm S _ _
      _ ≤ distanceSum S d (distanceSum S a (distanceSum S v w)) :=
        distanceSum_mono_right hd
          (hpos _ (hS a ha e he)).le hevMonotone
      _ = distanceSum S (distanceSum S a (distanceSum S v w)) d :=
        distanceSum_comm S _ _
  have hAssoc :
      distanceSum S (distanceSum S a (distanceSum S v w)) d =
        distanceSum S (distanceSum S a v) (distanceSum S w d) := by
    calc
      distanceSum S (distanceSum S a (distanceSum S v w)) d =
          distanceSum S (distanceSum S (distanceSum S a v) w) d := by
        rw [hassoc a ha v hv w hw]
      _ = distanceSum S (distanceSum S a v) (distanceSum S w d) :=
        hassoc (distanceSum S a v) (hS a ha v hv) w hw d hd
  calc
    x ≤ distanceSum S t d := hxtRounded
    _ ≤ distanceSum S (distanceSum S a e) d := htaMonotone
    _ ≤ distanceSum S (distanceSum S a (distanceSum S v w)) d := hInner
    _ = distanceSum S (distanceSum S a v) (distanceSum S w d) := hAssoc
    _ ≤ distanceSum S a v + distanceSum S w d :=
      distanceSum_le_add
        (hS a ha v hv) (hpos _ (hS w hw d hd)).le

end AllThoseRamseyClasses.Applications.MetricSaturation
