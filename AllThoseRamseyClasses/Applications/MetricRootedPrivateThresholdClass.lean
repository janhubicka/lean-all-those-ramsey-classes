import AllThoseRamseyClasses.Applications.MetricRootedSharedThresholdClass
import AllThoseRamseyClasses.Applications.MetricRootedJumpRootWitness

/-!
# Private jump classes remain wholly on their original metric side

The already verified identified-root shortest-path metric has exact
j-class unions above each common root vertex. This file supplies the
complement: a proper-jump class of U or V that contains NO common root
vertex remains entirely on that side.

The proof uses the full two-side coverage of the actual amalgam,
exact old-side isometries, and the source-matched proper-jump
cross/root witness from MetricRootedJumpRootWitness. In particular,
we do not infer the conclusion from the ordinary root-cut order,
which is known not to preserve jump convexity.

Together with metricRooted_rootThresholdClass_eq_union, these
statements give both cases of the finite metric jump-class
decomposition needed for recursively constructing a convex order.
No convex order or auxiliary closure-function amalgamation is
asserted in this file.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- If the j-class of x in the LEFT metric side avoids the common
root, then its COMPLETE j-class in the glued S-metric is exactly
the image of that original class. In particular it never picks up
a vertex of the opposite private side. -/
theorem metricRooted_privateLeftThresholdClass_eq
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (j : ℝ) (hj : Jump S j)
    (x : U)
    (hNoRoot : ∀ a : A, ¬ dU x (iU a) ≤ j) :
    {p : MetricRootedAmalgamVertex iU iV |
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedLeft iU iV hiU x) ≤ j} =
      metricRootedLeft iU iV hiU '' {y : U | dU y x ≤ j} := by
  ext p
  constructor
  · intro hp
    change metricRootedShortestDistance S iU iV dU dV
      p (metricRootedLeft iU iV hiU x) ≤ j at hp
    rcases metricRooted_covers iU iV hiU hiV p with
      ⟨y, hy⟩ | ⟨z, hz⟩
    · have hDist := hp
      rw [← hy,
        metricRootedShortestDistance_left_isometry
          S iU iV hiU dU dV y x] at hDist
      exact ⟨y, hDist, hy⟩
    · have hzx :
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedRight iU iV hiV z)
          (metricRootedLeft iU iV hiU x) ≤ j := by
        rw [hz]
        exact hp
      have hxz :
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedLeft iU iV hiU x)
          (metricRootedRight iU iV hiV z) ≤ j := by
        calc
          metricRootedShortestDistance S iU iV dU dV
              (metricRootedLeft iU iV hiU x)
              (metricRootedRight iU iV hiV z) =
            metricRootedShortestDistance S iU iV dU dV
              (metricRootedRight iU iV hiV z)
              (metricRootedLeft iU iV hiU x) :=
              metricRootedShortestDistance_symm iU iV hdU hdV _ _
          _ ≤ j := hzx
      obtain ⟨a, hxa, _⟩ :=
        (metricRootedCross_le_jump_iff_root
          hpos hS hassoc iU iV hiU hiV
          hdU hdV hBase j hj x z).mp hxz
      exact False.elim (hNoRoot a hxa)
  · rintro ⟨y, hy, rfl⟩
    change metricRootedShortestDistance S iU iV dU dV
      (metricRootedLeft iU iV hiU y)
      (metricRootedLeft iU iV hiU x) ≤ j
    rw [metricRootedShortestDistance_left_isometry
      S iU iV hiU dU dV y x]
    exact hy

/-- The symmetric statement for RIGHT-side private jump classes.
The assumption that the class avoids the root is expressed with
the root-to-right distance to match the proved cross-root
witness. No other side or common-root vertex is added. -/
theorem metricRooted_privateRightThresholdClass_eq
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (j : ℝ) (hj : Jump S j)
    (z : V)
    (hNoRoot : ∀ a : A, ¬ dV (iV a) z ≤ j) :
    {p : MetricRootedAmalgamVertex iU iV |
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedRight iU iV hiV z) ≤ j} =
      metricRootedRight iU iV hiV '' {y : V | dV y z ≤ j} := by
  ext p
  constructor
  · intro hp
    change metricRootedShortestDistance S iU iV dU dV
      p (metricRootedRight iU iV hiV z) ≤ j at hp
    rcases metricRooted_covers iU iV hiU hiV p with
      ⟨x, hx⟩ | ⟨y, hy⟩
    · have hxz :
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedLeft iU iV hiU x)
          (metricRootedRight iU iV hiV z) ≤ j := by
        rw [hx]
        exact hp
      obtain ⟨a, _, haz⟩ :=
        (metricRootedCross_le_jump_iff_root
          hpos hS hassoc iU iV hiU hiV
          hdU hdV hBase j hj x z).mp hxz
      exact False.elim (hNoRoot a haz)
    · have hDist := hp
      rw [← hy,
        metricRootedShortestDistance_right_isometry
          S iU iV hiV dU dV hBase y z] at hDist
      exact ⟨y, hDist, hy⟩
  · rintro ⟨y, hy, rfl⟩
    change metricRootedShortestDistance S iU iV dU dV
      (metricRootedRight iU iV hiV y)
      (metricRootedRight iU iV hiV z) ≤ j
    rw [metricRootedShortestDistance_right_isometry
      S iU iV hiV dU dV hBase y z]
    exact hy

end AllThoseRamseyClasses.Applications.MetricSaturation
