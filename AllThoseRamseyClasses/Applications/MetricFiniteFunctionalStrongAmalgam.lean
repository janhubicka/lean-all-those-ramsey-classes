import AllThoseRamseyClasses.Applications.MetricRootedFunctionalJumpClosure
import AllThoseRamseyClasses.Applications.MetricPaperBlockConvexStrongPushout

/-!
# Complete nonempty-root strong amalgamation of the finite metric F_j lift

This theorem assembles the ACTUAL printed class axioms, rather than
merely metric strong amalgamation or a pointwise partial-function
gluing fact.

Assume finite four-values S, finite convexly ordered S-metrics A,U,V,
with isometric order embeddings of A into U,V, and partial unary
functions F_j on all three sources. For EVERY proper jump j, the
F_j operations of U and V satisfy the printed designated-last
closure-class law, and their restrictions to the common root A
agree EXACTLY as partial functions, including undefinedness.

Then the identified-root shortest-path metric carrier W possesses:
* one linear order extending both given orders and convex at ALL
  paper block equivalences;
* the genuine S-metric with exact old-side isometric embeddings
  and no identifications other than the common root;
* simultaneously glued F_j for ALL jumps, preserving all old
  function graphs and undefined values under both embeddings;
* the FULL printed j-class closure law for every proper jump.

The complete local weak-candidate completion cutoff and the
original bounded-nonmetric-cycle proof in the 2019 paper remain
separate obligations. This theorem covers NONEMPTY common roots;
the empty-root separated-sum case is a separate construction.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Full finite nonempty-root metric-functional strong amalgamation,
including all literal partial F_j class laws and exact induced
old-side function restrictions. No hypothetical metric class-key
or closure-vertex witness remains in the assumptions. -/
theorem metricRooted_finiteS_functionalStrongAmalgam_exists
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
      dV (iV a) (iV b) = dA a b)
    (fA : ℝ → A → Option A)
    (fU : ℝ → U → Option U)
    (fV : ℝ → V → Option V)
    (hExtU : ∀ j : ℝ, Jump S j → ∀ a : A,
      fU j (iU a) = Option.map iU (fA j a))
    (hExtV : ∀ j : ℝ, Jump S j → ∀ a : A,
      fV j (iV a) = Option.map iV (fA j a))
    (hLawU : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw dU (fU j) j)
    (hLawV : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw dV (fV j) j) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
      (fW : ℝ → MetricRootedAmalgamVertex iU iV →
        Option (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiUOrder.injective x)
          (metricRootedLeft iU iV hiUOrder.injective y)) ∧
      (∀ z t : V, z < t →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiVOrder.injective z)
          (metricRootedRight iU iV hiVOrder.injective t)) ∧
      (@PaperBlockConvex (MetricRootedAmalgamVertex iU iV) o S
        (metricRootedShortestDistance S iU iV dU dV)) ∧
      MetricOn S (metricRootedShortestDistance S iU iV dU dV) ∧
      (∀ j : ℝ, Jump S j →
        @MetricJumpClosureLaw (MetricRootedAmalgamVertex iU iV) o
          (metricRootedShortestDistance S iU iV dU dV)
          (fW j) j) ∧
      (∀ j : ℝ, Jump S j → ∀ x : U,
        fW j (metricRootedLeft iU iV hiUOrder.injective x) =
          Option.map (metricRootedLeft iU iV hiUOrder.injective)
            (fU j x)) ∧
      (∀ j : ℝ, Jump S j → ∀ z : V,
        fW j (metricRootedRight iU iV hiVOrder.injective z) =
          Option.map (metricRootedRight iU iV hiVOrder.injective)
            (fV j z)) ∧
      (∀ x : U, ∀ z : V,
        metricRootedLeft iU iV hiUOrder.injective x =
          metricRootedRight iU iV hiVOrder.injective z ↔
          ∃ a : A, x = iU a ∧ z = iV a) := by
  classical
  obtain ⟨o, hOrdU, hOrdV, hBlock, hMetric,
      _hInjectU, _hInjectV, hOverlap, _hIsoU, _hIsoV⟩ :=
    metricRooted_finiteS_paperBlockConvexStrongAmalgam_exists
      hfinite hpos h4 hdA hdU hdV hconvU hconvV
      iU iV hiUOrder hiVOrder hiUDist hiVDist
  let W := MetricRootedAmalgamVertex iU iV
  let fW (j : ℝ) : W → Option W :=
    metricRootedPartialFunction iU iV
      hiUOrder.injective hiVOrder.injective (fU j) (fV j)
  have hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b) := by
    intro a b
    exact (hiUDist a b).trans (hiVDist a b).symm
  have hWell : WellDefined S :=
    wellDefined_of_finite hfinite hpos
  have hAssoc : AssociativeOn S :=
    associativeOn_of_fourValues hpos hWell h4
  refine ⟨o, fW, hOrdU, hOrdV, hBlock, hMetric,
    ?_, ?_, ?_, hOverlap⟩
  · intro j hj
    exact metricRootedPartialFunction_preserves_jumpClosureLaw
      hpos hWell hAssoc
      iU iV hiUOrder.injective hiVOrder.injective
      hdU hdV hBase o hOrdU hOrdV j hj
      (fA j) (fU j) (fV j)
      (hExtU j hj) (hExtV j hj)
      (hLawU j hj) (hLawV j hj)
  · intro j hj x
    exact metricRootedPartialFunction_left
      iU iV hiUOrder.injective hiVOrder.injective
      (fU j) (fV j) x
  · intro j hj z
    have hRoot := metricRootedPartialFunction_root_agree_of_source
      iU iV hiUOrder.injective hiVOrder.injective
      (fA j) (fU j) (fV j) (hExtU j hj) (hExtV j hj)
    exact metricRootedPartialFunction_right
      iU iV hiUOrder.injective hiVOrder.injective
      (fU j) (fV j) hRoot z

end AllThoseRamseyClasses.Applications.MetricSaturation
