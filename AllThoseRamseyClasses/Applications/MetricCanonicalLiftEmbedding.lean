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


/-- **The metric embedding part of the paper's lift.** An exact
isometry between original S-metric spaces preserves every distance
between original and canonical closure-class vertices, including
all mixed-level and class-pair sandwich distances.

This theorem needs no finite-set hypothesis: the canonical
distance formula and quotient-label invariance already make
sense for any S with well-defined associative rounded sums.
When finite S,V,W ensure both lifts are genuine metrics, this
is a genuine isometric embedding of the paper's metric shadows.
-/
theorem mapCanonicalLift_isometry {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y) :
    ∀ a b : V ⊕ CanonicalJumpTag hpos hS hdV,
      canonicalDistance hpos hS hdW
        (mapCanonicalLift hpos hS hdV hdW f hf a)
        (mapCanonicalLift hpos hS hdV hdW f hf b) =
      canonicalDistance hpos hS hdV a b := by
  intro a b
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          simpa only [mapCanonicalLift_old, canonicalDistance_old] using
            hf x y
      | inr tag =>
          have hclass := mapCanonicalJumpTag_class_mk
            hpos hS hdV hdW f hf tag (canonicalTagRoot tag)
              (canonicalTagRoot_class tag)
          have htarget := canonicalDistance_mixed_anyRoot
            hpos hS hassoc hdW
            (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)
            (f (canonicalTagRoot tag)) (f x) hclass
          calc
            canonicalDistance hpos hS hdW
                (mapCanonicalLift hpos hS hdV hdW f hf (.inl x))
                (mapCanonicalLift hpos hS hdV hdW f hf (.inr tag)) =
              canonicalDistance hpos hS hdW
                (.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
                (.inl (f x)) := by
                  simp only [mapCanonicalLift_old, mapCanonicalLift_tag,
                    canonicalDistance_old_new, canonicalDistance_new_old]
            _ = sumWithZero S
                  (canonicalTagLevel
                    (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
                  (dW (f (canonicalTagRoot tag)) (f x)) := htarget
            _ = sumWithZero S (canonicalTagLevel tag)
                  (dV (canonicalTagRoot tag) x) := by
                    rw [mapCanonicalJumpTag_level, hf]
            _ = canonicalDistance hpos hS hdV (.inl x) (.inr tag) :=
                (canonicalDistance_old_new hpos hS hdV tag x).symm
  | inr tag =>
      cases b with
      | inl x =>
          have hclass := mapCanonicalJumpTag_class_mk
            hpos hS hdV hdW f hf tag (canonicalTagRoot tag)
              (canonicalTagRoot_class tag)
          have htarget := canonicalDistance_mixed_anyRoot
            hpos hS hassoc hdW
            (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)
            (f (canonicalTagRoot tag)) (f x) hclass
          calc
            canonicalDistance hpos hS hdW
                (mapCanonicalLift hpos hS hdV hdW f hf (.inr tag))
                (mapCanonicalLift hpos hS hdV hdW f hf (.inl x)) =
              canonicalDistance hpos hS hdW
                (.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
                (.inl (f x)) := rfl
            _ = sumWithZero S
                  (canonicalTagLevel
                    (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
                  (dW (f (canonicalTagRoot tag)) (f x)) := htarget
            _ = sumWithZero S (canonicalTagLevel tag)
                  (dV (canonicalTagRoot tag) x) := by
                    rw [mapCanonicalJumpTag_level, hf]
            _ = canonicalDistance hpos hS hdV (.inr tag) (.inl x) :=
                (canonicalDistance_new_old hpos hS hdV tag x).symm
      | inr other =>
          by_cases heq : tag = other
          · subst other
            simp only [mapCanonicalLift_tag, canonicalDistance_new_diag]
          · have hne :
                mapCanonicalJumpTag hpos hS hdV hdW f hf tag ≠
                  mapCanonicalJumpTag hpos hS hdV hdW f hf other :=
              fun h => heq
                (mapCanonicalJumpTag_injective hpos hS hdV hdW f hf h)
            have hclassA := mapCanonicalJumpTag_class_mk
              hpos hS hdV hdW f hf tag (canonicalTagRoot tag)
                (canonicalTagRoot_class tag)
            have hclassB := mapCanonicalJumpTag_class_mk
              hpos hS hdV hdW f hf other (canonicalTagRoot other)
                (canonicalTagRoot_class other)
            have htarget := canonicalDistance_cross_anyRoots
              hpos hS hassoc hdW
                (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)
                (mapCanonicalJumpTag hpos hS hdV hdW f hf other)
                hne (f (canonicalTagRoot tag))
                (f (canonicalTagRoot other)) hclassA hclassB
            calc
              canonicalDistance hpos hS hdW
                  (mapCanonicalLift hpos hS hdV hdW f hf (.inr tag))
                  (mapCanonicalLift hpos hS hdV hdW f hf (.inr other)) =
                canonicalDistance hpos hS hdW
                  (.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
                  (.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf other)) :=
                    rfl
              _ = sumWithZero S
                    (sumWithZero S
                      (canonicalTagLevel
                        (mapCanonicalJumpTag hpos hS hdV hdW f hf tag))
                      (dW (f (canonicalTagRoot tag))
                        (f (canonicalTagRoot other))))
                    (canonicalTagLevel
                      (mapCanonicalJumpTag hpos hS hdV hdW f hf other)) :=
                  htarget
              _ = sumWithZero S
                    (sumWithZero S (canonicalTagLevel tag)
                      (dV (canonicalTagRoot tag) (canonicalTagRoot other)))
                    (canonicalTagLevel other) := by
                  rw [mapCanonicalJumpTag_level,
                    mapCanonicalJumpTag_level, hf]
              _ = canonicalDistance hpos hS hdV
                    (.inr tag) (.inr other) :=
                  (canonicalDistance_new_new hpos hS hdV tag other heq).symm

/-- The canonical lift of an exact isometry is injective whenever
the source canonical distance has its certified metric axioms.
This avoids an additional assumption that the original map or
its lifted map is injective: both follow from distance preservation
and positive off-diagonal S-distances. -/
theorem mapCanonicalLift_injective {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (hmetric : MetricOn S (canonicalDistance hpos hS hdV)) :
    Function.Injective (mapCanonicalLift hpos hS hdV hdW f hf) := by
  intro a b hab
  by_contra hne
  have hp : canonicalDistance hpos hS hdV a b ∈ S :=
    hmetric.values a b hne
  have hiso := mapCanonicalLift_isometry hpos hS hassoc
    hdV hdW f hf a b
  have hzero : canonicalDistance hpos hS hdW
      (mapCanonicalLift hpos hS hdV hdW f hf a)
      (mapCanonicalLift hpos hS hdV hdW f hf b) = 0 := by
    rw [hab]
    cases (mapCanonicalLift hpos hS hdV hdW f hf b) with
    | inl x => exact hdW.diag x
    | inr t => exact canonicalDistance_new_diag hpos hS hdW t
  have hz : canonicalDistance hpos hS hdV a b = 0 := by
    rw [← hiso]
    exact hzero
  have hp0 : 0 ∈ S := hz ▸ hp
  exact (not_lt_of_ge (le_refl (0 : ℝ))) (hpos 0 hp0)

end AllThoseRamseyClasses.Applications.MetricSaturation
