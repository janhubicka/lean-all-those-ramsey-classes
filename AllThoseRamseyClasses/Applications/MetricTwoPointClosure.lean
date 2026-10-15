import AllThoseRamseyClasses.Applications.MetricOnePointClosure
import AllThoseRamseyClasses.Applications.MetricJumpQuotient

/-!
# Two successive metric closure vertices

A complete S-metric admits closure vertices at any two positive jumps
j,k with roots r,s. Attach the j-vertex first and the k-vertex next,
using the original vertex s as root of the second attachment.

The resulting space has carrier Option (Option V):
  some (some x) = original x,
  some none     = first closure vertex at j,
  none          = second closure vertex at k.

Its distance between the two closure vertices is exactly
j ⊕_S d(r,s) ⊕_S k, matching the quotient-invariant label
certified in MetricJumpQuotient. No original distance changes.
Swapping the order of the two attachments gives the same cross
distance. This is a two-vertex metric step, not the full tagged
multi-level lift or its order and embedding properties.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A pair of closure vertices, built by two actual one-point
metric extensions; no abstract metric-completion axiom is used. -/
noncomputable def twoPointDistance (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (r s : V) (j k : ℝ) :
    Option (Option V) → Option (Option V) → ℝ :=
  onePointDistance S (onePointDistance S d r j) (some s) k

/-- The two-closure construction is an actual S-metric, by applying
the already checked one-point theorem twice. -/
theorem twoPointDistance_metric {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j k : ℝ} (hj : Jump S j) (hk : Jump S k)
    (r s : V) :
    MetricOn S (twoPointDistance S d r s j k) := by
  exact onePointDistance_metric hpos hS hassoc
    (onePointDistance_metric hpos hS hassoc hd hj r)
    hk (some s)

/-- Both attachments leave every original distance unchanged. -/
@[simp] theorem twoPointDistance_old {S : Set ℝ} {V : Type u}
    (d : V → V → ℝ) (r s : V) (j k : ℝ) (x y : V) :
    twoPointDistance S d r s j k (some (some x)) (some (some y)) =
      d x y := rfl

/-- The first closure representative keeps its distances to originals
after the second attachment. -/
@[simp] theorem twoPointDistance_first_original {S : Set ℝ} {V : Type u}
    (d : V → V → ℝ) (r s : V) (j k : ℝ) (x : V) :
    twoPointDistance S d r s j k (some none) (some (some x)) =
      sumWithZero S j (d r x) := rfl

/-- The second closure representative has the expected distances
to originals, irrespective of the first attachment. -/
@[simp] theorem twoPointDistance_second_original {S : Set ℝ} {V : Type u}
    (d : V → V → ℝ) (r s : V) (j k : ℝ) (x : V) :
    twoPointDistance S d r s j k none (some (some x)) =
      sumWithZero S k (d s x) := rfl

/-- Exact cross-distance between two different closure vertices. -/
@[simp] theorem twoPointDistance_closure_cross {S : Set ℝ} {V : Type u}
    (d : V → V → ℝ) (r s : V) (j k : ℝ) :
    twoPointDistance S d r s j k (some none) none =
      sumWithZero S (sumWithZero S j (d r s)) k := rfl

/-- This cross-distance is the previously certified quotient label,
so it depends only on the two jump classes of the roots. -/
theorem twoPointDistance_eq_quotientLabel {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j k : ℝ} (hj : Jump S j) (hk : Jump S k)
    (r s : V) :
    twoPointDistance S d r s j k (some none) none =
      quotientSandwichLabel hpos hS hassoc hd j k (Or.inr hj) (Or.inr hk)
        (Quotient.mk (jumpSetoid hpos hS hd j (Or.inr hj)) r)
        (Quotient.mk (jumpSetoid hpos hS hd k (Or.inr hk)) s) := by
  rw [quotientSandwichLabel_mk]
  rfl

/-- The first closure vertex remains at distance exactly j from
every member of its original j-threshold class. -/
theorem twoPointDistance_first_to_class {S : Set ℝ} {V : Type u}
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j)
    (r s : V) (k : ℝ) (x : V) (hx : d r x ≤ j) :
    twoPointDistance S d r s j k (some none) (some (some x)) = j := by
  exact onePointDistance_to_class hpos hd hj r x hx

/-- The second closure vertex is at distance exactly k from every
member of the original k-threshold class. -/
theorem twoPointDistance_second_to_class {S : Set ℝ} {V : Type u}
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (r s : V) (j : ℝ) {k : ℝ} (hk : Jump S k)
    (x : V) (hx : d s x ≤ k) :
    twoPointDistance S d r s j k none (some (some x)) = k := by
  exact onePointDistance_to_class hpos hd hk s x hx

/-- The cross-distance is unchanged when the two attachments are
performed in the opposite order, after identifying which new vertex
belongs to which jump level. -/
theorem twoPointDistance_cross_swap {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j k : ℝ} (hj : Jump S j) (hk : Jump S k)
    (r s : V) :
    twoPointDistance S d r s j k (some none) none =
      twoPointDistance S d s r k j (some none) none := by
  change sumWithZero S (sumWithZero S j (d r s)) k =
    sumWithZero S (sumWithZero S k (d s r)) j
  calc
    sumWithZero S (sumWithZero S j (d r s)) k =
        sumWithZero S k (sumWithZero S j (d r s)) :=
      sumWithZero_comm S (sumWithZero S j (d r s)) k
    _ = sumWithZero S k (sumWithZero S (d r s) j) := by
      rw [sumWithZero_comm S j (d r s)]
    _ = sumWithZero S (sumWithZero S k (d r s)) j :=
      (sumWithZero_assoc hpos hS hassoc
        (Or.inr hk.1) (metric_value_mem hd r s) (Or.inr hj.1)).symm
    _ = sumWithZero S (sumWithZero S k (d s r)) j := by
      rw [hd.symm r s]

end AllThoseRamseyClasses.Applications.MetricSaturation
