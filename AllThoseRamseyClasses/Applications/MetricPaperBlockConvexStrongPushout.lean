import AllThoseRamseyClasses.Applications.MetricFiniteConvexStrongPushout
import AllThoseRamseyClasses.Applications.MetricBlockConvexity
import AllThoseRamseyClasses.Applications.MetricRootedAmalgamOverlap

/-!
# Strong amalgamation in the manuscript's EXACT finite S-metric order language

The manuscript requires linear orders convex for its literal
block equivalences, not merely an abstract ordered partition.

For finite four-values S these block-convex orders are exactly
the proper-jump-convex orders, already established in
MetricBlockConvexity. We now combine that equivalence with the
completely constructive finite rooted jump-convex pushout,
the checked S-metric, both original-side isometries, and exact
common-root-only intersection.

The single public statement gives an actual finite S-metric
strong amalgam carrying a linear order extending both old
orders and satisfying the original printed PaperBlockConvex
predicate. It imposes NO hypothetical key existence assumption.

This theorem concerns ordinary ordered S-metric spaces, not the
auxiliary functional lift M_S^+ with partial F_j operations.
The printed local weak-completion cutoff and nonmetric-cycle
proof are independent obligations, not consequences here.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Exact metric strong amalgamation, including the paper's literal
block-convexity, for a NONEMPTY common root and finite four-values S.
The two old structures embed isometrically and preserve their full
linear orders, and their images meet precisely in the old root. -/
theorem metricRooted_finiteS_paperBlockConvexStrongAmalgam_exists
    {S : Set ℝ}
    (hfinite : S.Finite)
    (hpos : Positive S)
    (h4 : FourValues S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A] [LinearOrder A]
    [Finite U] [LinearOrder U]
    [Finite V] [LinearOrder V]
    {dA : A → A → ℝ}
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdA : MetricOn S dA)
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hconvU : PaperBlockConvex S dU)
    (hconvV : PaperBlockConvex S dV)
    (iU : A → U) (iV : A → V)
    (hiUOrder : StrictMono iU)
    (hiVOrder : StrictMono iV)
    (hiUDist : ∀ a b : A,
      dU (iU a) (iU b) = dA a b)
    (hiVDist : ∀ a b : A,
      dV (iV a) (iV b) = dA a b) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiUOrder.injective x)
          (metricRootedLeft iU iV hiUOrder.injective y)) ∧
      (∀ x y : V, x < y →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiVOrder.injective x)
          (metricRootedRight iU iV hiVOrder.injective y)) ∧
      (@PaperBlockConvex (MetricRootedAmalgamVertex iU iV) o S
        (metricRootedShortestDistance S iU iV dU dV)) ∧
      MetricOn S (metricRootedShortestDistance S iU iV dU dV) ∧
      Function.Injective
        (metricRootedLeft iU iV hiUOrder.injective) ∧
      Function.Injective
        (metricRootedRight iU iV hiVOrder.injective) ∧
      (∀ x : U, ∀ z : V,
        metricRootedLeft iU iV hiUOrder.injective x =
          metricRootedRight iU iV hiVOrder.injective z ↔
          ∃ a : A, x = iU a ∧ z = iV a) ∧
      (∀ x y : U,
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedLeft iU iV hiUOrder.injective x)
          (metricRootedLeft iU iV hiUOrder.injective y) =
            dU x y) ∧
      (∀ z t : V,
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedRight iU iV hiVOrder.injective z)
          (metricRootedRight iU iV hiVOrder.injective t) =
            dV z t) := by
  have hWell : WellDefined S :=
    wellDefined_of_finite hfinite hpos
  have hAssoc : AssociativeOn S :=
    associativeOn_of_fourValues hpos hWell h4
  have hJumpU : JumpConvex S dU :=
    (paperBlockConvex_iff_jumpConvex
      hfinite hpos h4 hdU).mp hconvU
  have hJumpV : JumpConvex S dV :=
    (paperBlockConvex_iff_jumpConvex
      hfinite hpos h4 hdV).mp hconvV
  obtain ⟨o, hOrderU, hOrderV, hJumpW⟩ :=
    metricRooted_finiteS_jumpConvexOrder_exists
      hfinite hpos hWell hAssoc
      hdA hdU hdV hJumpU hJumpV
      iU iV hiUOrder hiVOrder hiUDist hiVDist
  have hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b) := by
    intro a b
    exact (hiUDist a b).trans (hiVDist a b).symm
  have hMetric : MetricOn S
      (metricRootedShortestDistance S iU iV dU dV) :=
    metricRootedShortestDistance_metric
      hpos hWell hAssoc
      iU iV hiUOrder.injective hiVOrder.injective
      hdU hdV hBase
  letI : LinearOrder (MetricRootedAmalgamVertex iU iV) := o
  have hBlock : @PaperBlockConvex
      (MetricRootedAmalgamVertex iU iV) o S
      (metricRootedShortestDistance S iU iV dU dV) :=
    (paperBlockConvex_iff_jumpConvex
      hfinite hpos h4 hMetric).mpr hJumpW
  refine ⟨o, hOrderU, hOrderV, hBlock, hMetric,
    metricRootedLeft_injective iU iV hiUOrder.injective,
    metricRootedRight_injective iU iV hiVOrder.injective,
    ?_, ?_, ?_⟩
  · intro x z
    exact metricRooted_sides_intersect_exactly_on_root
      iU iV hiUOrder.injective hiVOrder.injective x z
  · intro x y
    exact metricRootedShortestDistance_left_isometry
      S iU iV hiUOrder.injective dU dV x y
  · intro z t
    exact metricRootedShortestDistance_right_isometry
      S iU iV hiVOrder.injective dU dV hBase z t

end AllThoseRamseyClasses.Applications.MetricSaturation
