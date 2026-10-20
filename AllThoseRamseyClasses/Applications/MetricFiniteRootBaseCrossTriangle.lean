import AllThoseRamseyClasses.Applications.MetricRoundedBaseCrossTriangle
import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossGeometry

/-!
# Real cross/base triangles for finite nonempty-root S-metric gluing

Let A be a finite nonempty metric base embedded in S-metrics U,V,
with identical base-pair distances. For x in U outside the base,
z in V outside the base and a in A, let

 δ(x,z) = min_{b∈A}(dU(x,iU b) ⊕_S dV(iV b,z)).

We prove the two important real triangle inequalities

  δ(x,z) ≤ dU(x,iU a) + dV(iV a,z),
  dU(x,iU a) ≤ δ(x,z) + dV(z,iV a).

The first follows by bounding the candidate path through a.
For the second, let b minimize δ. When a=b, use the
positive lower bound of the rounded path and nonnegativity.
When a≠b, the injective base embedding makes the old base
edge S-valued; agreement of base metrics, triangles in U
and V, and the scalar rounded base-cross inequality finish.

These lemmas are exactly the geometric root/cross triangles
needed by the genuine identified-base pushout. Their mirror
under exchanging U,V can be obtained later from the verified
cross-distance symmetry theorem. They do not by themselves
assert a complete glued metric or Ramsey property.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- An attained finite rounded shortest path cannot be longer
than the ordinary two-edge path through ANY chosen base point. -/
theorem finiteMetricBaseCrossDistance_le_base_path
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (x : U) (z : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hz : ∀ a : A, iV a ≠ z)
    (a : A) :
    finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
      dU x (iU a) + dV (iV a) z := by
  calc
    finiteMetricBaseCrossDistance S dU dV iU iV x z ≤
        distanceSum S (dU x (iU a)) (dV (iV a) z) :=
      finiteBaseShortestDistance_le S
        (fun b => dU x (iU b)) (fun b => dV (iV b) z) a
    _ ≤ dU x (iU a) + dV (iV a) z :=
      distanceSum_le_add
        (hdU.values x (iU a) (hx a))
        (hpos _ (hdV.values (iV a) z (hz a))).le

/-- A base point a and a left off-base point x cannot be brought
closer by passing through the opposite side's off-base point z.
The candidate minimizing point b may be different from a.

This is an ORDINARY metric triangle involving an actual base
vertex, with compatibility of the two source metrics on A
explicitly assumed. -/
theorem finiteMetricBaseCrossDistance_left_base_triangle
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (x : U) (z : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hz : ∀ a : A, iV a ≠ z)
    (a : A) :
    dU x (iU a) ≤
      finiteMetricBaseCrossDistance S dU dV iU iV x z +
      dV z (iV a) := by
  let b : A :=
    finiteBaseShortestPoint S
      (fun t => dU x (iU t))
      (fun t => dV (iV t) z)
  change dU x (iU a) ≤
    distanceSum S (dU x (iU b)) (dV (iV b) z) +
    dV z (iV a)
  by_cases hab : a = b
  · rw [hab]
    have hLow : dU x (iU b) ≤
        distanceSum S (dU x (iU b)) (dV (iV b) z) :=
      left_le_distanceSum
        (hdU.values x (iU b) (hx b))
        (hpos _ (hdV.values (iV b) z (hz b))).le
    have hNonneg : 0 ≤ dV z (iV b) :=
      (hpos _ (hdV.values z (iV b) (Ne.symm (hz b)))).le
    exact hLow.trans (le_add_of_nonneg_right hNonneg)
  · have hneq : iU b ≠ iU a := by
      intro heq
      exact hab ((hiU heq).symm)
    have hTriLeft : dU x (iU a) ≤
        dU x (iU b) + dU (iU b) (iU a) :=
      hdU.triangle x (iU b) (iU a)
    have hTriBridge :
        dU (iU b) (iU a) ≤
          dV (iV b) z + dV z (iV a) := by
      calc
        dU (iU b) (iU a) =
            dV (iV b) (iV a) := hBase b a
        _ ≤ dV (iV b) z + dV z (iV a) :=
          hdV.triangle (iV b) z (iV a)
    exact distanceSum_base_cross_triangle_bound
      hpos hS hassoc
      (hdU.values x (iU a) (hx a))
      (hdU.values x (iU b) (hx b))
      (hdU.values (iU b) (iU a) hneq)
      (hdV.values (iV b) z (hz b))
      (hdV.values z (iV a) (Ne.symm (hz a)))
      hTriLeft hTriBridge

end AllThoseRamseyClasses.Applications.MetricSaturation
