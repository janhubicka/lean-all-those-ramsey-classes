import AllThoseRamseyClasses.Applications.MetricFunctionalClosureTargets
import AllThoseRamseyClasses.Applications.MetricRootedPartialFunctions
import AllThoseRamseyClasses.Applications.MetricRootedSharedThresholdClass

/-!
# Every defined glued F_j value reaches a genuine closure point

An induced closed-root extension of the same partial F_j over
two convexly ordered S-metrics has an exactly defined glued
Option-valued partial function on the identified-base carrier.

A defined value of the glued function MUST point to a vertex
where the same function is undefined. The source closure laws
also force the original vertex to precede that target, and
the two points to be at EXACT distance j in the glued metric.

This handles all original/root/private vertices at once
because both side embeddings cover the entire carrier and
are exactly isometric. The complementary statement about
every other j-class member of an undefined point is handled
separately before deducing the complete classwise law.

These lemmas do not claim the original weak local-completion
cutoff or any published bounded-cycle argument.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- One exact shared F_j partial function on the root:
its defined values on the glued carrier always reach an
undefined, later vertex at exact shortest-path distance j. -/
theorem metricRootedPartialFunction_some_target
    (S : Set ℝ)
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
    (fA : A → Option A)
    (fU : U → Option U) (fV : V → Option V)
    (hExtU : ∀ a : A,
      fU (iU a) = Option.map iU (fA a))
    (hExtV : ∀ a : A,
      fV (iV a) = Option.map iV (fA a))
    (hLawU : MetricJumpClosureLaw dU fU j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (p c : MetricRootedAmalgamVertex iU iV)
    (hSome : metricRootedPartialFunction
       iU iV hiU hiV fU fV p = some c) :
    metricRootedPartialFunction
      iU iV hiU hiV fU fV c = none ∧
    @LT.lt _ o.toLT p c ∧
    metricRootedShortestDistance S iU iV dU dV p c = j := by
  have hRoot :=
    metricRootedPartialFunction_root_agree_of_source
      iU iV hiU hiV fA fU fV hExtU hExtV
  rcases metricRooted_covers iU iV hiU hiV p with
    ⟨x, hx⟩ | ⟨z, hz⟩
  · subst p
    rw [metricRootedPartialFunction_left
      iU iV hiU hiV fU fV x] at hSome
    cases hfx : fU x with
    | none =>
        simp [hfx] at hSome
    | some y =>
        rw [hfx] at hSome
        simp only [Option.map_some] at hSome
        have hc :
            c = metricRootedLeft iU iV hiU y :=
          (Option.some.inj hSome).symm
        subst c
        obtain ⟨hyNone, hxy, hDist⟩ :=
          metricJumpClosureLaw_some_is_target
            hpos hdU j hj fU hLawU x y hfx
        refine ⟨?_, hOrderU x y hxy, ?_⟩
        · rw [metricRootedPartialFunction_left
            iU iV hiU hiV fU fV y, hyNone]
          rfl
        · rw [metricRootedShortestDistance_left_isometry
            S iU iV hiU dU dV x y]
          exact hDist
  · subst p
    rw [metricRootedPartialFunction_right
      iU iV hiU hiV fU fV hRoot z] at hSome
    cases hfz : fV z with
    | none =>
        simp [hfz] at hSome
    | some y =>
        rw [hfz] at hSome
        simp only [Option.map_some] at hSome
        have hc :
            c = metricRootedRight iU iV hiV y :=
          (Option.some.inj hSome).symm
        subst c
        obtain ⟨hyNone, hzy, hDist⟩ :=
          metricJumpClosureLaw_some_is_target
            hpos hdV j hj fV hLawV z y hfz
        refine ⟨?_, hOrderV z y hzy, ?_⟩
        · rw [metricRootedPartialFunction_right
            iU iV hiU hiV fU fV hRoot y, hyNone]
          rfl
        · rw [metricRootedShortestDistance_right_isometry
            S iU iV hiV dU dV hBase z y]
          exact hDist

end AllThoseRamseyClasses.Applications.MetricSaturation
