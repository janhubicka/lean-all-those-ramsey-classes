import AllThoseRamseyClasses.Applications.MetricFiniteRootBaseCrossTriangle
import AllThoseRamseyClasses.Applications.MetricFiniteRootTwoCrossRight

/-!
# Mirrored base/cross triangle for genuine metric amalgamation

For two S-metric spaces with compatible finite nonempty base
embeddings, one of the remaining mixed metric triangles is
  dV(iV a,z) ≤ dU(iU a,x) + δ(x,z)
for off-root x∈U and z∈V and arbitrary a∈A.

The verified left-hand cross/base triangle is robust under
exchanging the two sides, but its oriented cross-distance
definition selects a priori different minimizing base points.
The independent `finiteMetricBaseCrossDistance_swap` theorem
identifies the actual minimum values using commutativity and
genuine metric symmetry, not equality of minimizers.

This completes the MIRRORED base/cross inequality, subject
to the injective right base embedding and exact agreement
of base distances. In conjunction with the existing left
base/cross and candidate path inequalities it gives all
metric triangles containing a single base vertex and one
genuinely cross-side edge. The entire pushout carrier's
metric triangle proof remains a separate assembly task.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- A base/right distance cannot be shortened by going from
that root point into the LEFT off-root side and back along
the finite minimum rounded cross path. This is the exact
mirrored base/cross triangle for the common finite root. -/
theorem finiteMetricBaseCrossDistance_right_base_triangle
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
    (x : U) (z : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hz : ∀ a : A, iV a ≠ z)
    (a : A) :
    dV (iV a) z ≤
      dU (iU a) x +
      finiteMetricBaseCrossDistance S dU dV iU iV x z := by
  have hBaseRev : ∀ a b : A,
      dV (iV a) (iV b) = dU (iU a) (iU b) :=
    fun a b => (hBase a b).symm
  have hSwapped :
      dV z (iV a) ≤
        finiteMetricBaseCrossDistance S dV dU iV iU z x +
        dU x (iU a) :=
    finiteMetricBaseCrossDistance_left_base_triangle
      hpos hS hassoc hdV hdU iV iU hiV
      hBaseRev z x
      (fun b => (hz b).symm)
      (fun b => (hx b).symm) a
  calc
    dV (iV a) z = dV z (iV a) :=
      hdV.symm (iV a) z
    _ ≤ finiteMetricBaseCrossDistance S dV dU iV iU z x +
        dU x (iU a) := hSwapped
    _ = dU (iU a) x +
        finiteMetricBaseCrossDistance S dU dV iU iV x z := by
      rw [← finiteMetricBaseCrossDistance_swap S
        hdU hdV iU iV x z,
        hdU.symm x (iU a), add_comm]

end AllThoseRamseyClasses.Applications.MetricSaturation
