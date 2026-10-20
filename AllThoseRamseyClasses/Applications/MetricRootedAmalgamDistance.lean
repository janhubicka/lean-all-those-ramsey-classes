import AllThoseRamseyClasses.Applications.MetricRootedAmalgamVertex
import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossGeometry

/-!
# Actual S-distance table on the identified finite nonempty-root carrier

The candidate gluing vertex type is
  A ⊕ (U \ iU(A)) ⊕ (V \ iV(A)),
with one literal copy of every base vertex. The distance table is:

* both vertices from the common root: the U-side base metric;
* both vertices from root + left: the ORIGINAL U-side metric;
* both vertices from root + right: the ORIGINAL V-side metric;
* left-off-base / right-off-base: the attained minimum
    δ(x,z) = min_{a∈A} (dU(x,iU(a)) ⊕_S dV(iV(a),z));
* equal vertices: the original zero diagonal.

This module PROVES the actual table has zero diagonal, symmetry,
and positive S-valued distances between distinct vertices under
injective root embeddings and genuine source metrics. In particular
the S-valuedness of offside cross distances uses the independently
verified finite shortest-path lemma, not a fictitious minimum over
an empty base.

The triangle axioms and full metric structure are the next
obligation; they will use the already verified one-cross and
two-cross triangles and the base-cross inequalities.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- The literal candidate metric on an identified-base gluing
carrier, using genuine old distances and attained S-rounded
cross paths. Its base is explicitly finite and nonempty. -/
noncomputable def metricRootedShortestDistance
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (dU : U → U → ℝ) (dV : V → V → ℝ) :
    MetricRootedAmalgamVertex iU iV →
      MetricRootedAmalgamVertex iU iV → ℝ
  | .inl a, .inl b => dU (iU a) (iU b)
  | .inl a, .inr (.inl x) => dU (iU a) x.val
  | .inr (.inl x), .inl a => dU x.val (iU a)
  | .inl a, .inr (.inr z) => dV (iV a) z.val
  | .inr (.inr z), .inl a => dV z.val (iV a)
  | .inr (.inl x), .inr (.inl y) => dU x.val y.val
  | .inr (.inr z), .inr (.inr t) => dV z.val t.val
  | .inr (.inl x), .inr (.inr z) =>
      finiteMetricBaseCrossDistance S dU dV iU iV x.val z.val
  | .inr (.inr z), .inr (.inl x) =>
      finiteMetricBaseCrossDistance S dU dV iU iV x.val z.val

@[simp] theorem metricRootedShortestDistance_root_root
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (a b : A) :
    metricRootedShortestDistance S iU iV dU dV (.inl a) (.inl b) =
      dU (iU a) (iU b) := rfl

@[simp] theorem metricRootedShortestDistance_cross
    (S : Set ℝ)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (x : MetricOutsideRoot iU) (z : MetricOutsideRoot iV) :
    metricRootedShortestDistance S iU iV dU dV
      (.inr (.inl x)) (.inr (.inr z)) =
    finiteMetricBaseCrossDistance S dU dV iU iV x.val z.val := rfl

/-- Zero diagonal for the actual identified-root distance table. -/
theorem metricRootedShortestDistance_diag
    {S : Set ℝ}
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (x : MetricRootedAmalgamVertex iU iV) :
    metricRootedShortestDistance S iU iV dU dV x x = 0 := by
  cases x with
  | inl a => exact hdU.diag (iU a)
  | inr t =>
      cases t with
      | inl x => exact hdU.diag x.val
      | inr z => exact hdV.diag z.val

/-- Metric symmetry for every root/root, root/side, same-side
and cross-side pair in the actual candidate amalgam. The
cross table uses identical δ(x,z) in both orientations. -/
theorem metricRootedShortestDistance_symm
    {S : Set ℝ}
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (x y : MetricRootedAmalgamVertex iU iV) :
    metricRootedShortestDistance S iU iV dU dV x y =
      metricRootedShortestDistance S iU iV dU dV y x := by
  cases x with
  | inl a =>
      cases y with
      | inl b => exact hdU.symm (iU a) (iU b)
      | inr t =>
          cases t with
          | inl b => exact hdU.symm (iU a) b.val
          | inr z => exact hdV.symm (iV a) z.val
  | inr t =>
      cases t with
      | inl x =>
          cases y with
          | inl a => exact hdU.symm x.val (iU a)
          | inr h =>
              cases h with
              | inl y => exact hdU.symm x.val y.val
              | inr z => rfl
      | inr z =>
          cases y with
          | inl a => exact hdV.symm z.val (iV a)
          | inr h =>
              cases h with
              | inl x => rfl
              | inr t => exact hdV.symm z.val t.val

/-- Every nonzero candidate amalgam distance lies in the
allowed positive S set. This is the exact non-collapse check
for offside vertices, not merely pseudometric nonnegativity. -/
theorem metricRootedShortestDistance_values
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (x y : MetricRootedAmalgamVertex iU iV)
    (hxy : x ≠ y) :
    metricRootedShortestDistance S iU iV dU dV x y ∈ S := by
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          have hab : a ≠ b := by
            intro hab
            exact hxy (congrArg Sum.inl hab)
          exact hdU.values (iU a) (iU b)
            (fun h => hab (hiU h))
      | inr t =>
          cases t with
          | inl u =>
              exact hdU.values (iU a) u.val (Ne.symm (u.property a))
          | inr z =>
              exact hdV.values (iV a) z.val (Ne.symm (z.property a))
  | inr t =>
      cases t with
      | inl u =>
          cases y with
          | inl a =>
              exact hdU.values u.val (iU a) (u.property a)
          | inr v =>
              cases v with
              | inl y =>
                  have hval : u.val ≠ y.val := by
                    intro huv
                    apply hxy
                    exact congrArg
                      (fun t : MetricOutsideRoot iU =>
                        (Sum.inr (Sum.inl t) :
                          MetricRootedAmalgamVertex iU iV))
                      (Subtype.ext huv)
                  exact hdU.values u.val y.val hval
              | inr z =>
                  exact (finiteMetricBaseCrossDistance_pos_mem
                    hpos hS hdU hdV iU iV u.val z.val
                    u.property (fun a => (z.property a).symm)).1
      | inr z =>
          cases y with
          | inl a =>
              exact hdV.values z.val (iV a) (z.property a)
          | inr v =>
              cases v with
              | inl u =>
                  exact (finiteMetricBaseCrossDistance_pos_mem
                    hpos hS hdU hdV iU iV u.val z.val
                    u.property (fun a => (z.property a).symm)).1
              | inr t =>
                  have hval : z.val ≠ t.val := by
                    intro hzt
                    apply hxy
                    exact congrArg
                      (fun t : MetricOutsideRoot iV =>
                        (Sum.inr (Sum.inr t) :
                          MetricRootedAmalgamVertex iU iV))
                      (Subtype.ext hzt)
                  exact hdV.values z.val t.val hval

end AllThoseRamseyClasses.Applications.MetricSaturation
