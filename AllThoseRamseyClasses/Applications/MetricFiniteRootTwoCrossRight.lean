import AllThoseRamseyClasses.Applications.MetricFiniteRootTwoCrossTriangle

/-!
# Right-side two-cross triangle via genuine metric symmetry

The same-side metric inequality
  d_U(x,y) ≤ δ(x,z) + δ(y,z)
in the compatible finite-base gluing construction is symmetric
under exchanging the two metric sides. However the finite-root
cross-distance is defined using two *oriented* metric legs and
a chosen minimizing base point. The minimizing point may differ
after exchanging U and V.

First prove that the ACTUAL attained cross distance is invariant
under side reversal by:
  (i)  the already verified commutativity of finite-base rounded
       shortest lengths, and
  (ii) symmetry of both source metrics, not a coincidence of
       chosen representatives.
Then apply the previous genuine U-side two-cross triangle with
U and V interchanged. This supplies the remaining two-cross
inequality for distinct off-base RIGHT vertices.

The metric base embeddings need only be injective on the side
whose within-side distance is being compared. This is a theorem
about cross distances, not yet the complete glued pushout metric.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Interchanging the two S-metric sides does not change the
minimum rounded cross-path length. The base minimum remains
finite and attained, and no equality of chosen minimizing
base points is assumed. -/
theorem finiteMetricBaseCrossDistance_swap
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (x : U) (z : V) :
    finiteMetricBaseCrossDistance S dU dV iU iV x z =
      finiteMetricBaseCrossDistance S dV dU iV iU z x := by
  unfold finiteMetricBaseCrossDistance
  have hV :
      (fun a : A => dV (iV a) z) =
        (fun a : A => dV z (iV a)) := by
    funext a
    exact hdV.symm (iV a) z
  have hU :
      (fun a : A => dU x (iU a)) =
        (fun a : A => dU (iU a) x) := by
    funext a
    exact hdU.symm x (iU a)
  calc
    finiteBaseShortestDistance S
        (fun a => dU x (iU a))
        (fun a => dV (iV a) z) =
      finiteBaseShortestDistance S
        (fun a => dV (iV a) z)
        (fun a => dU x (iU a)) :=
      finiteBaseShortestDistance_comm S
        (fun a => dU x (iU a))
        (fun a => dV (iV a) z)
    _ = finiteBaseShortestDistance S
          (fun a => dV z (iV a))
          (fun a => dU (iU a) x) := by
      rw [hV, hU]

/-- Two distinct off-base RIGHT vertices also satisfy the
two-cross triangle against any off-base LEFT vertex. This is
the exact mirrored geometric triangle, including coinciding
right vertices and arbitrary finite nonempty root embeddings. -/
theorem finiteMetricBaseCrossDistance_twoCross_triangle_right
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (z t : V) (x : U)
    (hz : ∀ a : A, z ≠ iV a)
    (ht : ∀ a : A, t ≠ iV a)
    (hx : ∀ a : A, iU a ≠ x) :
    dV z t ≤
      finiteMetricBaseCrossDistance S dU dV iU iV x z +
      finiteMetricBaseCrossDistance S dU dV iU iV x t := by
  have hBaseRev : ∀ a b : A,
      dV (iV a) (iV b) = dU (iU a) (iU b) :=
    fun a b => (hBase a b).symm
  have hOrig :
      dV z t ≤
        finiteMetricBaseCrossDistance S dV dU iV iU z x +
        finiteMetricBaseCrossDistance S dV dU iV iU t x :=
    finiteMetricBaseCrossDistance_twoCross_triangle_left
      hpos hS hassoc hdV hdU iV iU
      hiV hBaseRev z t x hz ht hx
  calc
    dV z t ≤
        finiteMetricBaseCrossDistance S dV dU iV iU z x +
        finiteMetricBaseCrossDistance S dV dU iV iU t x :=
      hOrig
    _ = finiteMetricBaseCrossDistance S dU dV iU iV x z +
        finiteMetricBaseCrossDistance S dU dV iU iV x t := by
      rw [← finiteMetricBaseCrossDistance_swap S hdU hdV iU iV x z,
        ← finiteMetricBaseCrossDistance_swap S hdU hdV iU iV x t]

end AllThoseRamseyClasses.Applications.MetricSaturation
