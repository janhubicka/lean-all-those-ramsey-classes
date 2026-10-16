import AllThoseRamseyClasses.Applications.MetricCanonicalLiftEmbedding
import AllThoseRamseyClasses.Applications.MetricCompletedClosureFunctions

/-!
# Natural transport of every completed jump-closure function

An exact original S-metric isometry f extends to the canonical metric
lift. The partial jump-closure functions on the WHOLE lifted carrier
must commute with this extension, not only on original vertices:
in particular lower-jump imaginaries acquire higher-jump F_j values.

This file proves the complete Option-valued function table is
preserved, including definedness and undefinedness. It uses
reflection of jump-quotient classes and the already verified
root-independent closure representatives, not a special choice of
Quotient.out on the target.

The order-preservation and class convexity parts of the paper's
lift remain separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- The target representative of the image of a canonical jump
tag belongs to the same old jump-equivalence class as the
image of the original representative of that source tag.
This comparison is independent of the choices made by Quotient.out. -/
theorem mapCanonicalJumpTag_root_threshold {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (tag : CanonicalJumpTag hpos hS hdV) :
    dW (canonicalTagRoot
          (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
       (f (canonicalTagRoot tag)) ≤ canonicalTagLevel tag := by
  let target := mapCanonicalJumpTag hpos hS hdV hdW f hf tag
  have htarget := canonicalTagRoot_class target
  have himage := mapCanonicalJumpTag_class_mk hpos hS
    hdV hdW f hf tag (canonicalTagRoot tag)
    (canonicalTagRoot_class tag)
  have hq :
      Quotient.mk
        (jumpSetoid hpos hS hdW tag.1.val
          (Or.inr tag.1.property))
        (canonicalTagRoot target) =
      Quotient.mk
        (jumpSetoid hpos hS hdW tag.1.val
          (Or.inr tag.1.property))
        (f (canonicalTagRoot tag)) := by
    exact htarget.trans himage.symm
  exact Quotient.exact hq

/-- The isometric canonical lift commutes with every completed
partial closure function F_j, including its Option-valued
definedness on all lower-, same-, and higher-level new
vertices. The result is a literal equality of partial values,
not merely preservation of function-graph relations. -/
theorem mapCanonicalLift_preserves_completedClosureValue {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (j : PositiveJumpLevel S)
    (a : V ⊕ CanonicalJumpTag hpos hS hdV) :
    Option.map (mapCanonicalLift hpos hS hdV hdW f hf)
        (canonicalCompletedClosureValue hpos hS hdV j a) =
      canonicalCompletedClosureValue hpos hS hdW j
        (mapCanonicalLift hpos hS hdV hdW f hf a) := by
  cases a with
  | inl x =>
      rfl
  | inr tag =>
      let target := mapCanonicalJumpTag hpos hS hdV hdW f hf tag
      have hlevelEq : canonicalTagLevel target =
          canonicalTagLevel tag :=
        mapCanonicalJumpTag_level hpos hS hdV hdW f hf tag
      by_cases hlevel : canonicalTagLevel tag < j.val
      · have htargetLevel : canonicalTagLevel target < j.val := by
          rw [hlevelEq]
          exact hlevel
        rw [canonicalCompletedClosureValue_lower hpos hS hdV
          j tag hlevel]
        rw [mapCanonicalLift_tag hpos hS hdV hdW f hf tag]
        rw [canonicalCompletedClosureValue_lower hpos hS hdW
          j target htargetLevel]
        change (some (Sum.inr
            (mapCanonicalJumpTag hpos hS hdV hdW f hf
              (canonicalClosureTag hpos hS hdV j
                (canonicalTagRoot tag)))) :
              Option (W ⊕ CanonicalJumpTag hpos hS hdW)) =
          (some (Sum.inr (canonicalClosureTag hpos hS hdW j
            (canonicalTagRoot target))) :
              Option (W ⊕ CanonicalJumpTag hpos hS hdW))
        have htagMap :
            mapCanonicalJumpTag hpos hS hdV hdW f hf
              (canonicalClosureTag hpos hS hdV j
                (canonicalTagRoot tag)) =
            canonicalClosureTag hpos hS hdW j
              (f (canonicalTagRoot tag)) := rfl
        rw [htagMap]
        have hroot := mapCanonicalJumpTag_root_threshold
          hpos hS hdV hdW f hf tag
        have hrootJ : dW (canonicalTagRoot target)
            (f (canonicalTagRoot tag)) ≤ j.val :=
          hroot.trans (le_of_lt hlevel)
        exact congrArg (fun t : CanonicalJumpTag hpos hS hdW =>
            (some (Sum.inr t) :
              Option (W ⊕ CanonicalJumpTag hpos hS hdW)))
          (canonicalClosureTag_eq_of_threshold hpos hS hdW j
            (f (canonicalTagRoot tag)) (canonicalTagRoot target)
            (by
              rw [hdW.symm (f (canonicalTagRoot tag))
                (canonicalTagRoot target)]
              exact hrootJ))
      · have hge : j.val ≤ canonicalTagLevel tag :=
          le_of_not_gt hlevel
        have htargetGe : j.val ≤ canonicalTagLevel target := by
          rw [hlevelEq]
          exact hge
        rw [canonicalCompletedClosureValue_ge hpos hS hdV j tag hge]
        change none =
          canonicalCompletedClosureValue hpos hS hdW j (.inr target)
        rw [canonicalCompletedClosureValue_ge hpos hS hdW
          j target htargetGe]

end AllThoseRamseyClasses.Applications.MetricSaturation
