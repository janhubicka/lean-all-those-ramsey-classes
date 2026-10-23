import AllThoseRamseyClasses.Applications.MetricRootedAmalgamVertex

/-!
# Exact gluing of partial functions on an identified-root carrier

Given partial unary functions F_U and F_V on old sides,
the glued partial function uses the left value on the common
root, and the original value on each private side.
It preserves both old restrictions, including undefinedness,
provided they agree after embedding values of common vertices.

Compatibility follows automatically when both old functions
extend the same partial function on the closed common root.
This is the function-carrier ingredient for the printed
S-metric functional lift; the metric and closure-last axioms
must still be checked separately.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

noncomputable def metricRootedPartialFunction
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (fU : U → Option U) (fV : V → Option V) :
    MetricRootedAmalgamVertex iU iV →
      Option (MetricRootedAmalgamVertex iU iV)
  | .inl a =>
      Option.map (metricRootedLeft iU iV hiU) (fU (iU a))
  | .inr (.inl x) =>
      Option.map (metricRootedLeft iU iV hiU) (fU x.val)
  | .inr (.inr z) =>
      Option.map (metricRootedRight iU iV hiV) (fV z.val)

/-- EXACT old left-side function equality, including undefinedness. -/
theorem metricRootedPartialFunction_left
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (fU : U → Option U) (fV : V → Option V)
    (x : U) :
    metricRootedPartialFunction iU iV hiU hiV fU fV
      (metricRootedLeft iU iV hiU x) =
      Option.map (metricRootedLeft iU iV hiU) (fU x) := by
  unfold metricRootedLeft
  generalize hp : (metricSideEquiv iU hiU).symm x = p
  have hOriginal : metricSideEquiv iU hiU p = x := by
    rw [← hp]
    exact (metricSideEquiv iU hiU).apply_symm_apply x
  cases p with
  | inl a =>
      change Option.map (metricRootedLeft iU iV hiU)
        (fU (iU a)) =
        Option.map (metricRootedLeft iU iV hiU) (fU x)
      rw [metricSideEquiv_inl] at hOriginal
      exact congrArg
        (fun t => Option.map (metricRootedLeft iU iV hiU) (fU t))
        hOriginal
  | inr y =>
      change Option.map (metricRootedLeft iU iV hiU)
        (fU y.val) =
        Option.map (metricRootedLeft iU iV hiU) (fU x)
      rw [metricSideEquiv_inr] at hOriginal
      exact congrArg
        (fun t => Option.map (metricRootedLeft iU iV hiU) (fU t))
        hOriginal

/-- EXACT old right-side function equality, including undefinedness. -/
theorem metricRootedPartialFunction_right
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (fU : U → Option U) (fV : V → Option V)
    (hRoot : ∀ a : A,
      Option.map (metricRootedLeft iU iV hiU) (fU (iU a)) =
        Option.map (metricRootedRight iU iV hiV) (fV (iV a)))
    (z : V) :
    metricRootedPartialFunction iU iV hiU hiV fU fV
      (metricRootedRight iU iV hiV z) =
      Option.map (metricRootedRight iU iV hiV) (fV z) := by
  unfold metricRootedRight
  generalize hp : (metricSideEquiv iV hiV).symm z = p
  have hOriginal : metricSideEquiv iV hiV p = z := by
    rw [← hp]
    exact (metricSideEquiv iV hiV).apply_symm_apply z
  cases p with
  | inl a =>
      change Option.map (metricRootedLeft iU iV hiU)
        (fU (iU a)) =
        Option.map (metricRootedRight iU iV hiV) (fV z)
      rw [metricSideEquiv_inl] at hOriginal
      exact (hRoot a).trans
        (congrArg
          (fun t => Option.map (metricRootedRight iU iV hiV) (fV t))
          hOriginal)
  | inr y =>
      change Option.map (metricRootedRight iU iV hiV)
        (fV y.val) =
        Option.map (metricRootedRight iU iV hiV) (fV z)
      rw [metricSideEquiv_inr] at hOriginal
      exact congrArg
        (fun t => Option.map (metricRootedRight iU iV hiV) (fV t))
        hOriginal

/-- A common closed source function induces the required
agreement after applying the two old side embeddings. -/
theorem metricRootedPartialFunction_root_agree_of_source
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (fA : A → Option A)
    (fU : U → Option U)
    (fV : V → Option V)
    (hU : ∀ a : A,
      fU (iU a) = Option.map iU (fA a))
    (hV : ∀ a : A,
      fV (iV a) = Option.map iV (fA a)) :
    ∀ a : A,
      Option.map (metricRootedLeft iU iV hiU) (fU (iU a)) =
        Option.map (metricRootedRight iU iV hiV) (fV (iV a)) := by
  intro a
  rw [hU a, hV a]
  cases h : fA a with
  | none =>
      simp [h]
  | some b =>
      simp only [h, Option.map_some]
      exact congrArg Option.some
        (metricRooted_sides_agree_on_root iU iV hiU hiV b)

end AllThoseRamseyClasses.Applications.MetricSaturation
