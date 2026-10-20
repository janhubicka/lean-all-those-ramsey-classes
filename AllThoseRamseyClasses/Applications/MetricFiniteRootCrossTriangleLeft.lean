import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossGeometry
import AllThoseRamseyClasses.Applications.MetricRoundedPathTriangle

/-!
# The first genuine triangle inequality for nonempty-base S-metric gluing

Consider two genuine S-metric spaces whose carriers contain copies
of one finite nonempty root A. For x,y on the left outside A and
z on the right outside A, let δ(x,z) be the attained minimum of
rounded paths through A:
  δ(x,z) = min_{a∈A} (dU(x,iU(a)) ⊕_S dV(iV(a),z)).
Then δ(x,z) ≤ dU(x,y) + δ(y,z).

This is a substantive ordinary REAL triangle inequality for the
proposed nonempty-base gluing metric, with no false assumption
that the rounded operation is ordinary addition. We choose the
actual minimizing base point for δ(y,z); the source left metric
triangle combined with the verified scalar inequality
  x ⊕_S c ≤ a + (b ⊕_S c)  when x≤a+b
gives the bound, and taking the minimum proves it for δ(x,z).

Zero-length left edges (x=y) are treated separately, since 0
need not belong to the allowed positive distance set S.

This module does NOT assume the two metrics already agree on the
root: that becomes essential for the remaining global pushout
triangles and within-side metric preservation. Its final theorem
is one of the mixed triangle inequalities, not full strong
amalgamation or a Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- One of the two essential mixed triangles of the genuine
nonempty-root shortest-path S-metric construction: two endpoints
on the left and one on the right. The result is asymmetric only
in presentation. Positivity and associative four-values rounded
sum are made explicit; in particular no fictitious S-zero. -/
theorem finiteMetricBaseCrossDistance_triangle_left
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (x y : U) (z : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hy : ∀ a : A, y ≠ iU a)
    (hz : ∀ a : A, iV a ≠ z) :
    finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
      dU x y + finiteMetricBaseCrossDistance S dU dV iU iV y z := by
  by_cases hxy : x = y
  · subst y
    rw [hdU.diag x, zero_add]
  · let a : A :=
      finiteBaseShortestPoint S
        (fun b => dU y (iU b))
        (fun b => dV (iV b) z)
    have hCrossX :
        finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
          distanceSum S (dU x (iU a)) (dV (iV a) z) :=
      finiteBaseShortestDistance_le S
        (fun b => dU x (iU b))
        (fun b => dV (iV b) z) a
    have hCrossY :
        finiteMetricBaseCrossDistance S dU dV iU iV y z =
          distanceSum S (dU y (iU a)) (dV (iV a) z) := rfl
    have hBound :
        distanceSum S (dU x (iU a)) (dV (iV a) z) ≤
          dU x y + distanceSum S (dU y (iU a)) (dV (iV a) z) :=
      distanceSum_triangle_path_bound hpos hS hassoc
        (hdU.values x (iU a) (hx a))
        (hdU.values x y hxy)
        (hdU.values y (iU a) (hy a))
        (hdV.values (iV a) z (hz a))
        (hdU.triangle x y (iU a))
    calc
      finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
          distanceSum S (dU x (iU a)) (dV (iV a) z) := hCrossX
      _ ≤ dU x y + distanceSum S (dU y (iU a)) (dV (iV a) z) :=
        hBound
      _ = dU x y + finiteMetricBaseCrossDistance S dU dV iU iV y z := by
        rw [hCrossY]

end AllThoseRamseyClasses.Applications.MetricSaturation
