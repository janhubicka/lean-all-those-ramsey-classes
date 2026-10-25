import AllThoseRamseyClasses.Applications.MetricRootedFunctionalJumpClosure
import AllThoseRamseyClasses.Applications.MetricPaperBlockConvexStrongPushout

/-!
# Strong amalgamation of finite convex metric functional lifts (nonempty root)

This packages the EXACT original block-convex metric strong
amalgamation with the whole classwise closure laws for every
partial unary function F_j indexed by a proper jump of finite S.

The source language is represented by a family of Option-valued
partial unary maps. Its literal functional axioms are expressed
by MetricJumpClosureLaw at EVERY proper jump j. An induced
root embedding preserves both function values and their
undefinedness, represented by Option.map.

The theorem constructs an actual finite identified-base S-metric
amalgam, with one order extending both old orders and convex
for the manuscript's BLOCK equivalences, and a family of glued
partial F_j functions. It proves source metric/order/function
restrictions, root-only intersection, and the entire original
closure-last/exact-j function law on the new carrier.

This is a different proof of the nonempty-root *strong
amalgamation axiom* from the short printed paragraph: all
functional class laws are checked rather than inferred solely
from the existence of a common root closure. It DOES NOT
prove the arbitrary weak-candidate local-completion condition,
the printed numerical cutoff, or the original cycle reductions
needed to infer Ramsey by the 2019 multiamalgamation theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- A family of partial F_j operations satisfies the source's
FULL printed closure law at every proper jump. -/
def MetricFunctionalJumpLaws
    {X : Type*} [LinearOrder X]
    (S : Set ℝ) (d : X → X → ℝ)
    (F : ℝ → X → Option X) : Prop :=
  ∀ j : ℝ, Jump S j → MetricJumpClosureLaw d (F j) j

/-- Complete strong metric + order + induced partial-function
amalgamation for the printed auxiliary F_j structure, over an
arbitrary NONEMPTY finite common root that is an induced
closed substructure of both finite convexly ordered sides.

No hypothetical class-key, closure-last or cross-witness
assumptions are imposed: all follow from the genuine source
metric and F_j axioms. -/
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
    (FA : ℝ → A → Option A)
    (FU : ℝ → U → Option U)
    (FV : ℝ → V → Option V)
    (hExtU : ∀ j : ℝ, ∀ a : A,
      FU j (iU a) = Option.map iU (FA j a))
    (hExtV : ∀ j : ℝ, ∀ a : A,
      FV j (iV a) = Option.map iV (FA j a))
    (hLawsU : MetricFunctionalJumpLaws S dU FU)
    (hLawsV : MetricFunctionalJumpLaws S dV FV) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
      (FW : ℝ → MetricRootedAmalgamVertex iU iV →
        Option (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiUOrder.injective x)
          (metricRootedLeft iU iV hiUOrder.injective y)) ∧
      (∀ z t : V, z < t →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiVOrder.injective z)
          (metricRootedRight iU iV hiVOrder.injective t)) ∧
      (@PaperBlockConvex (MetricRootedAmalgamVertex iU iV)
        o S (metricRootedShortestDistance S iU iV dU dV)) ∧
      MetricOn S (metricRootedShortestDistance S iU iV dU dV) ∧
      (∀ x y : U,
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedLeft iU iV hiUOrder.injective x)
          (metricRootedLeft iU iV hiUOrder.injective y) =
          dU x y) ∧
      (∀ z t : V,
        metricRootedShortestDistance S iU iV dU dV
          (metricRootedRight iU iV hiVOrder.injective z)
          (metricRootedRight iU iV hiVOrder.injective t) =
          dV z t) ∧
      (∀ x : U, ∀ z : V,
        metricRootedLeft iU iV hiUOrder.injective x =
          metricRootedRight iU iV hiVOrder.injective z ↔
        ∃ a : A, x = iU a ∧ z = iV a) ∧
      (@MetricFunctionalJumpLaws
        (MetricRootedAmalgamVertex iU iV) o S
        (metricRootedShortestDistance S iU iV dU dV) FW) ∧
      (∀ j : ℝ, ∀ x : U,
        FW j (metricRootedLeft iU iV hiUOrder.injective x) =
          Option.map (metricRootedLeft iU iV hiUOrder.injective)
            (FU j x)) ∧
      (∀ j : ℝ, ∀ z : V,
        FW j (metricRootedRight iU iV hiVOrder.injective z) =
          Option.map (metricRootedRight iU iV hiVOrder.injective)
            (FV j z)) := by
  have hWell : WellDefined S :=
    wellDefined_of_finite hfinite hpos
  have hAssoc : AssociativeOn S :=
    associativeOn_of_fourValues hpos hWell h4
  obtain ⟨o, hOrderU, hOrderV, hBlock, hMetric,
    _hInjU, _hInjV, hIntersect,
    hIsomU, hIsomV⟩ :=
    metricRooted_finiteS_paperBlockConvexStrongAmalgam_exists
      hfinite hpos h4 hdA hdU hdV hconvU hconvV
      iU iV hiUOrder hiVOrder hiUDist hiVDist
  have hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b) := by
    intro a b
    exact (hiUDist a b).trans (hiVDist a b).symm
  let W := MetricRootedAmalgamVertex iU iV
  let FW : ℝ → W → Option W :=
    fun j => metricRootedPartialFunction
      iU iV hiUOrder.injective hiVOrder.injective
      (FU j) (FV j)
  refine ⟨o, FW, hOrderU, hOrderV, hBlock,
    hMetric, hIsomU, hIsomV, hIntersect,
    ?_, ?_, ?_⟩
  · intro j hj
    exact metricRootedPartialFunction_preserves_jumpClosureLaw
      hpos hWell hAssoc
      iU iV hiUOrder.injective hiVOrder.injective
      hdU hdV hBase o hOrderU hOrderV j hj
      (FA j) (FU j) (FV j)
      (hExtU j) (hExtV j)
      (hLawsU j hj) (hLawsV j hj)
  · intro j x
    exact metricRootedPartialFunction_left
      iU iV hiUOrder.injective hiVOrder.injective
      (FU j) (FV j) x
  · intro j z
    have hRoot :=
      metricRootedPartialFunction_root_agree_of_source
        iU iV hiUOrder.injective hiVOrder.injective
        (FA j) (FU j) (FV j)
        (hExtU j) (hExtV j)
    exact metricRootedPartialFunction_right
      iU iV hiUOrder.injective hiVOrder.injective
      (FU j) (FV j) hRoot z

end AllThoseRamseyClasses.Applications.MetricSaturation
