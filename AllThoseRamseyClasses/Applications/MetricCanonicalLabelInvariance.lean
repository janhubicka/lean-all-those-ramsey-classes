import AllThoseRamseyClasses.Applications.MetricCanonicalDistance
import AllThoseRamseyClasses.Applications.MetricJumpQuotient

/-!
# Canonical closure metric values depend only on quotient classes

The explicit canonicalDistance construction uses Quotient.out to
choose one representative from each original jump-equivalence
class. This module certifies that the metric formulas themselves
depend on the quotient classes, not on those arbitrary roots.

The previously proved quotientSandwichLabel is defined by a genuine
two-variable quotient lift, so its values are representative
independent. Identify canonicalDistance on each new-old and
distinct new-new pair with this quotient label. Consequently
any representatives of those classes give the same distance.

These results are useful for extending an isometric embedding
to closure-class imaginaries. They do not yet prove the extension
map, its order preservation, or any Ramsey-class application.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- An original vertex paired with a class tag has a metric
distance determined by their two quotient classes, not by
the representative chosen by Quotient.out. -/
theorem canonicalDistance_mixed_quotientLabel {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) (x : V) :
    canonicalDistance hpos hS hd (.inr tag) (.inl x) =
      quotientSandwichLabel hpos hS hassoc hd
        (canonicalTagLevel tag) 0
        (Or.inr (canonicalTagLevel_jump tag)) (Or.inl rfl)
        tag.2
        (Quotient.mk (jumpSetoid hpos hS hd 0 (Or.inl rfl)) x) := by
  rw [canonicalDistance_new_old]
  rw [← canonicalTagRoot_class tag]
  rw [quotientSandwichLabel_mk]
  simp only [sumWithZero_zero_right]

/-- Two distinct canonical closure tags have their cross-distance
given by the genuine two-quotient sandwich label. -/
theorem canonicalDistance_cross_quotientLabel {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd) (hab : a ≠ b) :
    canonicalDistance hpos hS hd (.inr a) (.inr b) =
      quotientSandwichLabel hpos hS hassoc hd
        (canonicalTagLevel a) (canonicalTagLevel b)
        (Or.inr (canonicalTagLevel_jump a))
        (Or.inr (canonicalTagLevel_jump b))
        a.2 b.2 := by
  rw [canonicalDistance_new_new hpos hS hd a b hab]
  rw [← canonicalTagRoot_class a, ← canonicalTagRoot_class b]
  rw [quotientSandwichLabel_mk]

/-- Replace the chosen root of one closure tag by *any* original
representative of that class without changing its distances to V. -/
theorem canonicalDistance_mixed_anyRoot {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) (u x : V)
    (hu : Quotient.mk
        (jumpSetoid hpos hS hd (canonicalTagLevel tag)
          (Or.inr (canonicalTagLevel_jump tag))) u = tag.2) :
    canonicalDistance hpos hS hd (.inr tag) (.inl x) =
      sumWithZero S (canonicalTagLevel tag) (d u x) := by
  rw [canonicalDistance_mixed_quotientLabel hpos hS hassoc hd tag x]
  rw [← hu]
  rw [quotientSandwichLabel_mk]
  simp only [sumWithZero_zero_right]

/-- Any representatives of two *distinct* canonical tags compute
the same cross-distance; equality of the class tags, rather than
equality of their chosen root points, determines the diagonal. -/
theorem canonicalDistance_cross_anyRoots {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd) (hab : a ≠ b)
    (u v : V)
    (hu : Quotient.mk
        (jumpSetoid hpos hS hd (canonicalTagLevel a)
          (Or.inr (canonicalTagLevel_jump a))) u = a.2)
    (hv : Quotient.mk
        (jumpSetoid hpos hS hd (canonicalTagLevel b)
          (Or.inr (canonicalTagLevel_jump b))) v = b.2) :
    canonicalDistance hpos hS hd (.inr a) (.inr b) =
      sumWithZero S
        (sumWithZero S (canonicalTagLevel a) (d u v))
        (canonicalTagLevel b) := by
  rw [canonicalDistance_cross_quotientLabel hpos hS hassoc hd a b hab]
  rw [← hu, ← hv]
  rw [quotientSandwichLabel_mk]

end AllThoseRamseyClasses.Applications.MetricSaturation
