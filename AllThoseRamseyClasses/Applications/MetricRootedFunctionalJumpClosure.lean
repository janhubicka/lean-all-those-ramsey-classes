import AllThoseRamseyClasses.Applications.MetricRootedFunctionalUndefinedPrivate
import AllThoseRamseyClasses.Applications.MetricFunctionalClosurePointwise

/-!
# Entire F_j closure law survives the finite rooted metric strong amalgam

This is the full classwise FUNCTIONAL jump law for one proper
jump j, not merely existence of a metric strong amalgam.

Given genuine S-metric source structures U and V with partial
unary F_j operations satisfying the printed closure law, and
exact induced agreement on a common CLOSED root A, the glued
Option-valued partial function satisfies that SAME original
law for EVERY vertex of the identified-base metric carrier.

The proof is modular:

1. A defined glued F_j reaches an undefined later target at
   exact shortest-path distance j.
2. An undefined shared-root closure governs its whole mixed
   jump class, with exact values from both source sides.
3. An undefined private closure has a root-disjoint j-class
   and governs the original side class with exact values.
4. The independently checked pointwise-to-classwise lemma
   reconstructs the complete original F_j class law.

No new closure vertex is freely invented. The theorem is
conditional ONLY on the source metric/functional axioms and
induced closed-root embeddings (and the ordinary compatible
extension of source orders). The 2019 bounded-nonmetric-cycle
and exact local weak-completion proof remains separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- A complete j-class closure law for the ACTUAL glued partial
unary function, including root/private cases and undefinedness,
follows from the same printed law on both original metric sides. -/
theorem metricRootedPartialFunction_preserves_jumpClosureLaw
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
    (hOrderU : ∀ x y : U, x < y →
      @LT.lt _ o.toLT
        (metricRootedLeft iU iV hiU x)
        (metricRootedLeft iU iV hiU y))
    (hOrderV : ∀ x y : V, x < y →
      @LT.lt _ o.toLT
        (metricRootedRight iU iV hiV x)
        (metricRootedRight iU iV hiV y))
    (j : ℝ) (hj : Jump S j)
    (fA : A → Option A)
    (fU : U → Option U) (fV : V → Option V)
    (hExtU : ∀ a : A,
      fU (iU a) = Option.map iU (fA a))
    (hExtV : ∀ a : A,
      fV (iV a) = Option.map iV (fA a))
    (hLawU : MetricJumpClosureLaw dU fU j)
    (hLawV : MetricJumpClosureLaw dV fV j) :
    @MetricJumpClosureLaw (MetricRootedAmalgamVertex iU iV) o
      (metricRootedShortestDistance S iU iV dU dV)
      (metricRootedPartialFunction iU iV hiU hiV fU fV) j := by
  let W := MetricRootedAmalgamVertex iU iV
  let dW : W → W → ℝ :=
    metricRootedShortestDistance S iU iV dU dV
  let fW : W → Option W :=
    metricRootedPartialFunction iU iV hiU hiV fU fV
  have hMetric : MetricOn S dW :=
    metricRootedShortestDistance_metric
      hpos hS hassoc iU iV hiU hiV hdU hdV hBase
  have hRoot :=
    metricRootedPartialFunction_root_agree_of_source
      iU iV hiU hiV fA fU fV hExtU hExtV
  exact @metricJumpClosureLaw_of_pointwise S hpos hS
    W o dW hMetric j hj fW
    (by
      intro p c hp
      exact metricRootedPartialFunction_some_target
        S hpos iU iV hiU hiV hdU hdV hBase
        o hOrderU hOrderV j hj
        fA fU fV hExtU hExtV hLawU hLawV p c hp)
    (by
      intro c hc p hDifferent hClose
      cases c with
      | inl a =>
          exact metricRootedPartialFunction_none_root_target
            S hpos iU iV hiU hiV hdU hdV hBase
            o hOrderU hOrderV j hj
            fA fU fV hExtU hExtV hLawU hLawV
            a hc p hDifferent hClose
      | inr side =>
          cases side with
          | inl x =>
              exact metricRootedPartialFunction_none_leftPrivate_target
                hpos hS hassoc iU iV hiU hiV hdU hdV hBase
                o hOrderU j hj fA fU fV hExtU hLawU
                x hc p hDifferent hClose
          | inr z =>
              exact metricRootedPartialFunction_none_rightPrivate_target
                hpos hS hassoc iU iV hiU hiV hdU hdV hBase
                o hOrderV j hj fA fU fV hExtV hRoot hLawV
                z hc p hDifferent hClose)

end AllThoseRamseyClasses.Applications.MetricSaturation
