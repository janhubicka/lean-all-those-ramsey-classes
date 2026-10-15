import AllThoseRamseyClasses.Applications.MetricCanonicalQuotientMap
import AllThoseRamseyClasses.Applications.MetricCanonicalLabelInvariance

/-!
# Extension of exact S-metric isometries to canonical closure imaginaries

An isometric embedding of original S-metric spaces induces maps on
their quotient classes at each jump level. This file extends the
original vertex map to the disjoint union with unique canonical
positive-jump equivalence classes.

An essential point is that the induced dependent tag map is injective:
the jump level is preserved and the class map at every fixed jump
reflects equality. Metric preservation further uses the verified
representative-independent sandwich formula, not an assumption
about the arbitrary Quotient.out roots.

The extension is a metric embedding. Its order preservation and
the paper's exact closure-function structure are separate checks.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- An exact original isometry induces an *injective* map of
canonical jump-class tags. No finiteness hypothesis is necessary. -/
theorem mapCanonicalJumpTag_injective {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y) :
    Function.Injective (mapCanonicalJumpTag hpos hS hdV hdW f hf) := by
  intro ⟨j, a⟩ ⟨k, b⟩ hab
  have hj : j = k := congrArg Sigma.fst hab
  subst k
  have hclasses :
      mapJumpClass hpos hS hdV hdW f hf j.val
          (Or.inr j.property) a =
        mapJumpClass hpos hS hdV hdW f hf j.val
          (Or.inr j.property) b := by
    injection hab with _ heq
    exact heq
  have heq := (mapJumpClass_injective hpos hS hdV hdW
    f hf j.val (Or.inr j.property)) hclasses
  cases heq
  rfl

/-- The canonical closure extension of an exact original isometry,
sending old vertices through f and class imaginaries through the
already verified quotient-class map. -/
noncomputable def mapCanonicalLift {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y) :
    (V ⊕ CanonicalJumpTag hpos hS hdV) →
      (W ⊕ CanonicalJumpTag hpos hS hdW)
  | .inl x => .inl (f x)
  | .inr tag => .inr (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)

@[simp] theorem mapCanonicalLift_old {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (x : V) :
    mapCanonicalLift hpos hS hdV hdW f hf (.inl x) = .inl (f x) := rfl

@[simp] theorem mapCanonicalLift_tag {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (tag : CanonicalJumpTag hpos hS hdV) :
    mapCanonicalLift hpos hS hdV hdW f hf (.inr tag) =
      .inr (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) := rfl

end AllThoseRamseyClasses.Applications.MetricSaturation
