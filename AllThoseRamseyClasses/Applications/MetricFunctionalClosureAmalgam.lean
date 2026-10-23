import AllThoseRamseyClasses.Applications.MetricFunctionalJumpClosureLaw
import AllThoseRamseyClasses.Applications.MetricRootedClosureLastPreservation

/-!
# Closure-last preservation from the ACTUAL partial F_j source law

The printed auxiliary metric class has partial unary functions
F_j. The source law says every j-class has one designated
last representative and all other members map to it at exact
distance j. The general lemma proves that an undefined
F_j value identifies this last vertex.

If the two source structures are closed extensions of one
common rooted partial function fA, an undefined root value
stays undefined on BOTH sides. The corresponding root
closure vertex is then last and at exact-j distance in the
whole glued class, by the separately verified metric
class-decomposition theorem. The private-side cases are
similar and do not use any root function.

This is a faithful bridge between the printed F_j axioms
and the earlier pure-metric closure-last lemmas. It does not
assert that the entire amalgam function has yet been proved
correct, or supply the weak exact local-completion cutoff.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- A common root vertex where the original root F_j is
undefined is still the last exact-j closure vertex of
its entire glued class, given induced source functions
and the source closure laws. -/
theorem metricRooted_sharedClosure_of_partialSource
    {S : Set ℝ}
    (hpos : Positive S)
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
    (fA : A → Option A) (fU : U → Option U)
    (fV : V → Option V)
    (hExtU : ∀ a : A, fU (iU a) = Option.map iU (fA a))
    (hExtV : ∀ a : A, fV (iV a) = Option.map iV (fA a))
    (hLawU : MetricJumpClosureLaw dU fU j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (c : A) (hNone : fA c = none)
    (p : MetricRootedAmalgamVertex iU iV)
    (hpClose :
      metricRootedShortestDistance S iU iV dU dV p (.inl c) ≤ j)
    (hpDifferent : p ≠ .inl c) :
    (@LT.lt _ o.toLT p (.inl c)) ∧
      metricRootedShortestDistance S iU iV dU dV p (.inl c) = j := by
  have hUNone : fU (iU c) = none :=
    rootClosure_none_preserved iU fA fU hExtU c hNone
  have hVNone : fV (iV c) = none :=
    rootClosure_none_preserved iV fA fV hExtV c hNone
  exact metricRooted_sharedClosureVertex_preserved
    S iU iV hiU hiV dU dV hBase
    o hOrderU hOrderV c j
    (metricJumpClosureLaw_none_is_last
      hpos hdU j hj fU hLawU (iU c) hUNone)
    (metricJumpClosureLaw_none_is_last
      hpos hdV j hj fV hLawV (iV c) hVNone)
    p hpClose hpDifferent

/-- For a root-disjoint LEFT class whose last vertex has
undefined F_j, the full glued class keeps that vertex last
at exact j-distance, from the original source closure axiom. -/
theorem metricRooted_privateLeftClosure_of_partialSource
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder U]
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
    (j : ℝ) (hj : Jump S j)
    (fU : U → Option U) (hLawU : MetricJumpClosureLaw dU fU j)
    (x : U) (hNoRoot : ∀ a : A, ¬ dU x (iU a) ≤ j)
    (hNone : fU x = none)
    (p : MetricRootedAmalgamVertex iU iV)
    (hpClose : metricRootedShortestDistance S iU iV dU dV
      p (metricRootedLeft iU iV hiU x) ≤ j)
    (hpDifferent : p ≠ metricRootedLeft iU iV hiU x) :
    (@LT.lt _ o.toLT p (metricRootedLeft iU iV hiU x)) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedLeft iU iV hiU x) = j := by
  exact metricRooted_privateLeftClosureVertex_preserved
    hpos hS hassoc iU iV hiU hiV hdU hdV hBase
    o hOrderU j hj x hNoRoot
    (metricJumpClosureLaw_none_is_last
      hpos hdU j hj fU hLawU x hNone)
    p hpClose hpDifferent

/-- Symmetric RIGHT-private source closure preservation. -/
theorem metricRooted_privateRightClosure_of_partialSource
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
    (hOrderV : ∀ x y : V, x < y →
      @LT.lt _ o.toLT
        (metricRootedRight iU iV hiV x)
        (metricRootedRight iU iV hiV y))
    (j : ℝ) (hj : Jump S j)
    (fV : V → Option V) (hLawV : MetricJumpClosureLaw dV fV j)
    (z : V) (hNoRoot : ∀ a : A, ¬ dV (iV a) z ≤ j)
    (hNone : fV z = none)
    (p : MetricRootedAmalgamVertex iU iV)
    (hpClose : metricRootedShortestDistance S iU iV dU dV
      p (metricRootedRight iU iV hiV z) ≤ j)
    (hpDifferent : p ≠ metricRootedRight iU iV hiV z) :
    (@LT.lt _ o.toLT p (metricRootedRight iU iV hiV z)) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (metricRootedRight iU iV hiV z) = j := by
  exact metricRooted_privateRightClosureVertex_preserved
    hpos hS hassoc iU iV hiU hiV hdU hdV hBase
    o hOrderV j hj z hNoRoot
    (metricJumpClosureLaw_none_is_last
      hpos hdV j hj fV hLawV z hNone)
    p hpClose hpDifferent

end AllThoseRamseyClasses.Applications.MetricSaturation
