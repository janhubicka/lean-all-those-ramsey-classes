import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossTriangleLeft

/-!
# The second one-side mixed metric triangle over a finite nonempty root

Symmetric to the verified-construction candidate for two LEFT points
and one RIGHT point: the shortest rounded cross distance from a
left-side vertex x to a right-side vertex z satisfies

  δ(x,z) ≤ δ(x,y) + dV(y,z)

for right-side y,z outside the common finite nonempty root.

The minimizing base point is chosen for δ(x,y). Its rounded path
to z can be bounded using dV(base,z) ≤ dV(base,y)+dV(y,z)
and the verified SCALAR right-handed rounded path inequality.
The case y=z is handled by the actual zero diagonal, not by
assuming that zero belongs to the positive distance set S.

Together with the left-handed inequality, these cover the mixed
triangles with exactly ONE cross-side distance as the conclusion.
The different case of a WITHIN-SIDE distance bounded by TWO cross
distances, the agreement of the old metrics over their common root,
and the complete metric pushout remain future obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Actual real metric triangle for two off-base right points
and one off-base left point, under the paper's positive
four-values / associative rounded-sum assumptions. -/
theorem finiteMetricBaseCrossDistance_triangle_right
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (x : U) (y z : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hy : ∀ a : A, iV a ≠ y)
    (hz : ∀ a : A, iV a ≠ z) :
    finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
      finiteMetricBaseCrossDistance S dU dV iU iV x y +
      dV y z := by
  by_cases hyz : y = z
  · subst z
    rw [hdV.diag y, add_zero]
  · let a : A :=
      finiteBaseShortestPoint S
        (fun b => dU x (iU b))
        (fun b => dV (iV b) y)
    have hCrossZ :
        finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
          distanceSum S (dU x (iU a)) (dV (iV a) z) :=
      finiteBaseShortestDistance_le S
        (fun b => dU x (iU b))
        (fun b => dV (iV b) z) a
    have hCrossY :
        finiteMetricBaseCrossDistance S dU dV iU iV x y =
          distanceSum S (dU x (iU a)) (dV (iV a) y) := rfl
    have hVtriangle :
        dV (iV a) z ≤ dV y z + dV (iV a) y := by
      calc
        dV (iV a) z ≤ dV (iV a) y + dV y z :=
          hdV.triangle (iV a) y z
        _ = dV y z + dV (iV a) y := add_comm _ _
    have hBound :
        distanceSum S (dU x (iU a)) (dV (iV a) z) ≤
          distanceSum S (dU x (iU a)) (dV (iV a) y) + dV y z :=
      distanceSum_triangle_path_bound_right hpos hS hassoc
        (hdV.values (iV a) z (hz a))
        (hdV.values y z hyz)
        (hdV.values (iV a) y (hy a))
        (hdU.values x (iU a) (hx a))
        hVtriangle
    calc
      finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
          distanceSum S (dU x (iU a)) (dV (iV a) z) := hCrossZ
      _ ≤ distanceSum S (dU x (iU a)) (dV (iV a) y) + dV y z :=
        hBound
      _ = finiteMetricBaseCrossDistance S dU dV iU iV x y + dV y z := by
        rw [hCrossY]

end AllThoseRamseyClasses.Applications.MetricSaturation
