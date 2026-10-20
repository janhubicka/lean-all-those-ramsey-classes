import AllThoseRamseyClasses.Applications.MetricRootedAmalgamDistance
import AllThoseRamseyClasses.Applications.MetricFiniteRootBaseCrossRight
import AllThoseRamseyClasses.Applications.MetricFiniteRootCrossTriangleRight

/-!
# All real metric triangles for the finite identified-base shortest-path gluing

For compatible metric embeddings of a finite nonempty base A into
S-metric spaces U,V, use the ACTUAL identified-base vertex carrier,
the OLD within-side distances, and rounded shortest cross distances.

All 27 location patterns for the triangle's three vertices are
explicitly considered: root / off-left / off-right. The within-side
cases use the real metric triangle in U or V. Mixed cases invoke the
separately verified one-cross, two-cross, and base-cross inequalities.
In particular, we never replace an S-rounded shortest path with a
fictitious ordinary sum, and neither direction of the cross distance
assumes that the chosen minimizing base points coincide.

The statement assumes both base maps injective and their exact
pairwise metric compatibility. The conclusion is the full MetricOn
property of this one finite nonempty-root carrier; it does not by
itself produce the convex linear order, partial functions F_j,
class-level strong amalgamation, or local Ramsey completion.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Every original/root/cross combination obeys the ORDINARY real
triangle inequality in the actual identified-base shortest-path
distance table. This does not invoke any nonmetric-cycle shortcut. -/
theorem metricRootedShortestDistance_triangle
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
    (x y z : MetricRootedAmalgamVertex iU iV) :
    metricRootedShortestDistance S iU iV dU dV x z ≤
      metricRootedShortestDistance S iU iV dU dV x y +
        metricRootedShortestDistance S iU iV dU dV y z := by
  let δ : U → V → ℝ := finiteMetricBaseCrossDistance S dU dV iU iV
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          cases z with
          | inl c =>
              -- RRR: R=root, L=left off-root, V=right off-root
              change dU (iU a) (iU c) ≤ dU (iU a) (iU b) + dU (iU b) (iU c)
              exact hdU.triangle (iU a) (iU b) (iU c)
          | inr w2 =>
            cases w2 with
            | inl c =>
                -- RRL: R=root, L=left off-root, V=right off-root
                change dU (iU a) c.val ≤ dU (iU a) (iU b) + dU (iU b) c.val
                exact hdU.triangle (iU a) (iU b) c.val
            | inr c =>
                -- RRV: R=root, L=left off-root, V=right off-root
                change dV (iV a) c.val ≤ dU (iU a) (iU b) + dV (iV b) c.val
                calc
                  dV (iV a) c.val ≤ dV (iV a) (iV b) + dV (iV b) c.val := hdV.triangle (iV a) (iV b) c.val
                  _ = dU (iU a) (iU b) + dV (iV b) c.val := by rw [hBase a b]
      | inr w1 =>
        cases w1 with
        | inl b =>
            cases z with
            | inl c =>
                -- RLR: R=root, L=left off-root, V=right off-root
                change dU (iU a) (iU c) ≤ dU (iU a) b.val + dU b.val (iU c)
                exact hdU.triangle (iU a) b.val (iU c)
            | inr w2 =>
              cases w2 with
              | inl c =>
                  -- RLL: R=root, L=left off-root, V=right off-root
                  change dU (iU a) c.val ≤ dU (iU a) b.val + dU b.val c.val
                  exact hdU.triangle (iU a) b.val c.val
              | inr c =>
                  -- RLV: R=root, L=left off-root, V=right off-root
                  change dV (iV a) c.val ≤ dU (iU a) b.val + δ b.val c.val
                  exact finiteMetricBaseCrossDistance_right_base_triangle hpos hS hassoc hdU hdV iU iV hiV hBase b.val c.val b.property (fun t => (c.property t).symm) a
        | inr b =>
            cases z with
            | inl c =>
                -- RVR: R=root, L=left off-root, V=right off-root
                change dU (iU a) (iU c) ≤ dV (iV a) b.val + dV b.val (iV c)
                calc
                  dU (iU a) (iU c) = dV (iV a) (iV c) := hBase a c
                  _ ≤ dV (iV a) b.val + dV b.val (iV c) := hdV.triangle (iV a) b.val (iV c)
            | inr w2 =>
              cases w2 with
              | inl c =>
                  -- RVL: R=root, L=left off-root, V=right off-root
                  change dU (iU a) c.val ≤ dV (iV a) b.val + δ c.val b.val
                  calc
                    dU (iU a) c.val = dU c.val (iU a) := hdU.symm (iU a) c.val
                    _ ≤ δ c.val b.val + dV b.val (iV a) := finiteMetricBaseCrossDistance_left_base_triangle hpos hS hassoc hdU hdV iU iV hiU hBase c.val b.val c.property (fun t => (b.property t).symm) a
                    _ = dV (iV a) b.val + δ c.val b.val := by rw [hdV.symm b.val (iV a), add_comm]
              | inr c =>
                  -- RVV: R=root, L=left off-root, V=right off-root
                  change dV (iV a) c.val ≤ dV (iV a) b.val + dV b.val c.val
                  exact hdV.triangle (iV a) b.val c.val
  | inr w0 =>
    cases w0 with
    | inl a =>
        cases y with
        | inl b =>
            cases z with
            | inl c =>
                -- LRR: R=root, L=left off-root, V=right off-root
                change dU a.val (iU c) ≤ dU a.val (iU b) + dU (iU b) (iU c)
                exact hdU.triangle a.val (iU b) (iU c)
            | inr w2 =>
              cases w2 with
              | inl c =>
                  -- LRL: R=root, L=left off-root, V=right off-root
                  change dU a.val c.val ≤ dU a.val (iU b) + dU (iU b) c.val
                  exact hdU.triangle a.val (iU b) c.val
              | inr c =>
                  -- LRV: R=root, L=left off-root, V=right off-root
                  change δ a.val c.val ≤ dU a.val (iU b) + dV (iV b) c.val
                  exact finiteMetricBaseCrossDistance_le_base_path hpos hdU hdV iU iV a.val c.val a.property (fun t => (c.property t).symm) b
        | inr w1 =>
          cases w1 with
          | inl b =>
              cases z with
              | inl c =>
                  -- LLR: R=root, L=left off-root, V=right off-root
                  change dU a.val (iU c) ≤ dU a.val b.val + dU b.val (iU c)
                  exact hdU.triangle a.val b.val (iU c)
              | inr w2 =>
                cases w2 with
                | inl c =>
                    -- LLL: R=root, L=left off-root, V=right off-root
                    change dU a.val c.val ≤ dU a.val b.val + dU b.val c.val
                    exact hdU.triangle a.val b.val c.val
                | inr c =>
                    -- LLV: R=root, L=left off-root, V=right off-root
                    change δ a.val c.val ≤ dU a.val b.val + δ b.val c.val
                    exact finiteMetricBaseCrossDistance_triangle_left hpos hS hassoc hdU hdV iU iV a.val b.val c.val a.property b.property (fun t => (c.property t).symm)
          | inr b =>
              cases z with
              | inl c =>
                  -- LVR: R=root, L=left off-root, V=right off-root
                  change dU a.val (iU c) ≤ δ a.val b.val + dV b.val (iV c)
                  exact finiteMetricBaseCrossDistance_left_base_triangle hpos hS hassoc hdU hdV iU iV hiU hBase a.val b.val a.property (fun t => (b.property t).symm) c
              | inr w2 =>
                cases w2 with
                | inl c =>
                    -- LVL: R=root, L=left off-root, V=right off-root
                    change dU a.val c.val ≤ δ a.val b.val + δ c.val b.val
                    exact finiteMetricBaseCrossDistance_twoCross_triangle_left hpos hS hassoc hdU hdV iU iV hiU hBase a.val c.val b.val a.property c.property (fun t => (b.property t).symm)
                | inr c =>
                    -- LVV: R=root, L=left off-root, V=right off-root
                    change δ a.val c.val ≤ δ a.val b.val + dV b.val c.val
                    exact finiteMetricBaseCrossDistance_triangle_right hpos hS hassoc hdU hdV iU iV a.val b.val c.val a.property (fun t => (b.property t).symm) (fun t => (c.property t).symm)
    | inr a =>
        cases y with
        | inl b =>
            cases z with
            | inl c =>
                -- VRR: R=root, L=left off-root, V=right off-root
                change dV a.val (iV c) ≤ dV a.val (iV b) + dU (iU b) (iU c)
                calc
                  dV a.val (iV c) ≤ dV a.val (iV b) + dV (iV b) (iV c) := hdV.triangle a.val (iV b) (iV c)
                  _ = dV a.val (iV b) + dU (iU b) (iU c) := by rw [hBase b c]
            | inr w2 =>
              cases w2 with
              | inl c =>
                  -- VRL: R=root, L=left off-root, V=right off-root
                  change δ c.val a.val ≤ dV a.val (iV b) + dU (iU b) c.val
                  calc
                    δ c.val a.val ≤ dU c.val (iU b) + dV (iV b) a.val := finiteMetricBaseCrossDistance_le_base_path hpos hdU hdV iU iV c.val a.val c.property (fun t => (a.property t).symm) b
                    _ = dV a.val (iV b) + dU (iU b) c.val := by rw [hdU.symm c.val (iU b), hdV.symm (iV b) a.val, add_comm]
              | inr c =>
                  -- VRV: R=root, L=left off-root, V=right off-root
                  change dV a.val c.val ≤ dV a.val (iV b) + dV (iV b) c.val
                  exact hdV.triangle a.val (iV b) c.val
        | inr w1 =>
          cases w1 with
          | inl b =>
              cases z with
              | inl c =>
                  -- VLR: R=root, L=left off-root, V=right off-root
                  change dV a.val (iV c) ≤ δ b.val a.val + dU b.val (iU c)
                  calc
                    dV a.val (iV c) = dV (iV c) a.val := hdV.symm a.val (iV c)
                    _ ≤ dU (iU c) b.val + δ b.val a.val := finiteMetricBaseCrossDistance_right_base_triangle hpos hS hassoc hdU hdV iU iV hiV hBase b.val a.val b.property (fun t => (a.property t).symm) c
                    _ = δ b.val a.val + dU b.val (iU c) := by rw [hdU.symm (iU c) b.val, add_comm]
              | inr w2 =>
                cases w2 with
                | inl c =>
                    -- VLL: R=root, L=left off-root, V=right off-root
                    change δ c.val a.val ≤ δ b.val a.val + dU b.val c.val
                    calc
                      δ c.val a.val ≤ dU c.val b.val + δ b.val a.val := finiteMetricBaseCrossDistance_triangle_left hpos hS hassoc hdU hdV iU iV c.val b.val a.val c.property b.property (fun t => (a.property t).symm)
                      _ = δ b.val a.val + dU b.val c.val := by rw [hdU.symm c.val b.val, add_comm]
                | inr c =>
                    -- VLV: R=root, L=left off-root, V=right off-root
                    change dV a.val c.val ≤ δ b.val a.val + δ b.val c.val
                    exact finiteMetricBaseCrossDistance_twoCross_triangle_right hpos hS hassoc hdU hdV iU iV hiV hBase a.val c.val b.val a.property c.property (fun t => (b.property t).symm)
          | inr b =>
              cases z with
              | inl c =>
                  -- VVR: R=root, L=left off-root, V=right off-root
                  change dV a.val (iV c) ≤ dV a.val b.val + dV b.val (iV c)
                  exact hdV.triangle a.val b.val (iV c)
              | inr w2 =>
                cases w2 with
                | inl c =>
                    -- VVL: R=root, L=left off-root, V=right off-root
                    change δ c.val a.val ≤ dV a.val b.val + δ c.val b.val
                    calc
                      δ c.val a.val ≤ δ c.val b.val + dV b.val a.val := finiteMetricBaseCrossDistance_triangle_right hpos hS hassoc hdU hdV iU iV c.val b.val a.val c.property (fun t => (b.property t).symm) (fun t => (a.property t).symm)
                      _ = dV a.val b.val + δ c.val b.val := by rw [hdV.symm b.val a.val, add_comm]
                | inr c =>
                    -- VVV: R=root, L=left off-root, V=right off-root
                    change dV a.val c.val ≤ dV a.val b.val + dV b.val c.val
                    exact hdV.triangle a.val b.val c.val

/-- The finite shortest-path table is an ACTUAL S-metric, not only
a symmetric table of S-valued entries. All 27 triangle cases
above are needed for this statement. -/
theorem metricRootedShortestDistance_metric
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
      dU (iU a) (iU b) = dV (iV a) (iV b)) :
    MetricOn S (metricRootedShortestDistance S iU iV dU dV) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact metricRootedShortestDistance_diag iU iV hdU hdV
  · exact metricRootedShortestDistance_values hpos hS iU iV hiU hdU hdV
  · exact metricRootedShortestDistance_symm iU iV hdU hdV
  · exact metricRootedShortestDistance_triangle hpos hS hassoc
      iU iV hiU hiV hdU hdV hBase

end AllThoseRamseyClasses.Applications.MetricSaturation
