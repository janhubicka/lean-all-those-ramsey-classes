import AllThoseRamseyClasses.Applications.MetricCompletedClosureFunctions
import AllThoseRamseyClasses.Applications.MetricCanonicalClassLastInLift

/-!
# Completed closure-function values have the required distance and class maximum

The canonical finite metric lift defines the partial function F_j on
original vertices and on smaller-level closure vertices. The target
of every defined value is the unique canonical j-class representative.

This module verifies the actual metric-and-order interface of these
values: for every F_j(a)=some b, the metric distance d(a,b) is exactly
j, and b is the last vertex of its *completed* j-equivalence class
(including any earlier smaller-jump closure vertices).

The remaining order-theoretic claim that each entire completed
j-class is an interval is independently formalized in the metric
convexity module. The present theorem uses only the already checked
last-class result and does not assume convexity to prove it.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- If F_j(a) is defined on the canonical lifted carrier, its value
is the designated last j-class representative and its metric edge
has precisely the prescribed jump length j. -/
theorem canonicalCompletedClosure_valid_edge {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S)
    (a b : V ⊕ CanonicalJumpTag hpos hS hd)
    (hvalue : canonicalCompletedClosureValue hpos hS hd j a =
      some b) :
    canonicalDistance hpos hS hd a b = j.val ∧
      (letI := canonicalInsertionLinearOrder hpos hS hd;
        ∀ z : V ⊕ CanonicalJumpTag hpos hS hd,
          canonicalDistance hpos hS hd b z ≤ j.val → z ≤ b) := by
  letI : LinearOrder (V ⊕ CanonicalJumpTag hpos hS hd) :=
    canonicalInsertionLinearOrder hpos hS hd
  cases a with
  | inl x =>
      rw [canonicalCompletedClosureValue_old] at hvalue
      injection hvalue with hb
      subst b
      constructor
      · calc
          canonicalDistance hpos hS hd (.inl x)
              (.inr (canonicalClosureTag hpos hS hd j x)) =
            canonicalDistance hpos hS hd
              (.inr (canonicalClosureTag hpos hS hd j x))
              (.inl x) := by
                rfl
          _ = j.val := canonicalClosureTag_distance hpos hS hd j x
      · intro z hz
        exact canonicalInsertion_closure_last_of_threshold
          hpos hS hd (canonicalClosureTag hpos hS hd j x) z hz
  | inr tag =>
      by_cases hlt : canonicalTagLevel tag < j.val
      · rw [canonicalCompletedClosureValue_lower hpos hS hd j tag hlt]
          at hvalue
        injection hvalue with hb
        subst b
        constructor
        · exact canonicalCompletedClosureValue_lower_distance
            hpos hS hd j tag hlt
        · intro z hz
          exact canonicalInsertion_closure_last_of_threshold
            hpos hS hd
            (canonicalClosureTag hpos hS hd j (canonicalTagRoot tag))
            z hz
      · have hge : j.val ≤ canonicalTagLevel tag := le_of_not_gt hlt
        rw [canonicalCompletedClosureValue_ge hpos hS hd j tag hge]
          at hvalue
        cases hvalue

end AllThoseRamseyClasses.Applications.MetricSaturation
