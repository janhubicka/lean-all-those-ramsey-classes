import AllThoseRamseyClasses.Applications.MetricRoundedTwoCrossTriangle
import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossGeometry

/-!
# The two-cross triangle of shortest-path metric gluing

Let A be a FINITE NONEMPTY metric base, fully embedded in two
S-metric spaces U and V with the SAME distances on base vertices.
For two vertices x,y outside the image of A on U and z outside
its image on V, consider the genuine finite minimum

  δ(x,z) = min_{a∈A} (dU(x,iU a) ⊕_S dV(iV a,z)).

We prove the missing ordinary real triangle inequality

  dU(x,y) ≤ δ(x,z) + δ(y,z).

The minimizing base vertices a and b for δ(x,z) and δ(y,z)
need not be the same. When a=b the result follows directly
from one triangle in U and the lower bounds of each rounded
sum. When a≠b, injectivity of the base embedding ensures
that dU(iU a,iU b) is a POSITIVE allowed S-distance. The two
source-side triangles and the bridge triangle through z
satisfy the hypotheses of the independently checked scalar
two-cross bound, which uses actual rounded associativity.

This explicitly avoids a WRONG argument based only on the
real inequality dU(x,y) ≤ u+v+w+t: rounding those four
operands separately can erase admissible intermediate values.

The theorem does not pretend that δ extends to a full metric
without defining its old/base/cross cases and checking every
pushout triangle. Symmetry gives the corresponding right-side
two-cross inequality as a later easy corollary.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- An original same-side distance cannot be shortened by a
two-cross path through the other side: the key new triangle of
the nonempty-base shortest-path S-metric amalgam.

Both old base embeddings preserve the SAME pairwise distances;
only the first embedding must be explicitly injective to make
the connecting base edge an allowed positive S-distance.
All vertices x,y,z are required to lie OFF the base images. -/
theorem finiteMetricBaseCrossDistance_twoCross_triangle_left
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
    (x y : U) (z : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hy : ∀ a : A, y ≠ iU a)
    (hz : ∀ a : A, iV a ≠ z) :
    dU x y ≤
      finiteMetricBaseCrossDistance S dU dV iU iV x z +
      finiteMetricBaseCrossDistance S dU dV iU iV y z := by
  by_cases hxy : x = y
  · subst y
    have hPositive :=
      (finiteMetricBaseCrossDistance_pos_mem
        hpos hS hdU hdV iU iV x z hx hz).2
    rw [hdU.diag x]
    exact add_nonneg (le_of_lt hPositive) (le_of_lt hPositive)
  · let a : A :=
      finiteBaseShortestPoint S
        (fun t => dU x (iU t))
        (fun t => dV (iV t) z)
    let b : A :=
      finiteBaseShortestPoint S
        (fun t => dU y (iU t))
        (fun t => dV (iV t) z)
    have hLeftA :
        dU x (iU a) ≤
          finiteMetricBaseCrossDistance S dU dV iU iV x z := by
      change dU x (iU a) ≤
        distanceSum S (dU x (iU a)) (dV (iV a) z)
      exact left_le_distanceSum
        (hdU.values x (iU a) (hx a))
        (hpos _ (hdV.values (iV a) z (hz a))).le
    have hLeftB :
        dU (iU b) y ≤
          finiteMetricBaseCrossDistance S dU dV iU iV y z := by
      rw [hdU.symm (iU b) y]
      change dU y (iU b) ≤
        distanceSum S (dU y (iU b)) (dV (iV b) z)
      exact left_le_distanceSum
        (hdU.values y (iU b) (hy b))
        (hpos _ (hdV.values (iV b) z (hz b))).le
    by_cases hab : a = b
    · subst b
      exact (hdU.triangle x (iU a) y).trans
        (add_le_add hLeftA hLeftB)
    · have hABne : iU a ≠ iU b := by
        intro heq
        exact hab (hiU heq)
      have hBaseEdge : dU (iU a) (iU b) ∈ S :=
        hdU.values (iU a) (iU b) hABne
      have hX : dU x y ∈ S :=
        hdU.values x y hxy
      have hT : dU x (iU b) ∈ S :=
        hdU.values x (iU b) (hx b)
      have hA : dU x (iU a) ∈ S :=
        hdU.values x (iU a) (hx a)
      have hD : dU (iU b) y ∈ S :=
        hdU.values (iU b) y (Ne.symm (hy b))
      have hV : dV (iV a) z ∈ S :=
        hdV.values (iV a) z (hz a)
      have hW : dV z (iV b) ∈ S :=
        hdV.values z (iV b) (Ne.symm (hz b))
      have hBridge :
          dU (iU a) (iU b) ≤
            dV (iV a) z + dV z (iV b) := by
        calc
          dU (iU a) (iU b) =
              dV (iV a) (iV b) := hBase a b
          _ ≤ dV (iV a) z + dV z (iV b) :=
            hdV.triangle (iV a) z (iV b)
      have hRounded :
          dU x y ≤
            distanceSum S (dU x (iU a)) (dV (iV a) z) +
            distanceSum S (dV z (iV b)) (dU (iU b) y) :=
        distanceSum_twoCross_triangle_bound hpos hS hassoc
          hX hT hA hBaseEdge hD hV hW
          (hdU.triangle x (iU b) y)
          (hdU.triangle x (iU a) (iU b))
          hBridge
      change dU x y ≤
        distanceSum S (dU x (iU a)) (dV (iV a) z) +
        distanceSum S (dU y (iU b)) (dV (iV b) z)
      calc
        dU x y ≤
            distanceSum S (dU x (iU a)) (dV (iV a) z) +
            distanceSum S (dV z (iV b)) (dU (iU b) y) :=
          hRounded
        _ = distanceSum S (dU x (iU a)) (dV (iV a) z) +
            distanceSum S (dU y (iU b)) (dV (iV b) z) := by
          rw [distanceSum_comm S (dV z (iV b)) (dU (iU b) y),
            hdU.symm (iU b) y, hdV.symm z (iV b)]

end AllThoseRamseyClasses.Applications.MetricSaturation
