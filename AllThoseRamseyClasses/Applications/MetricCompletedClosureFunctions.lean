import AllThoseRamseyClasses.Applications.MetricCanonicalClosureFunctions

/-!
# Higher-jump closure functions on *all* canonical lifted vertices

The original-vertex closure function has already been certified.
For the full paper's functional metric lift, smaller-level closure
representatives belonging to a higher-jump class must also map
to the corresponding higher-jump closure representative.

This module defines a partial function at each positive proper
jump j on the entire duplicate-free lifted carrier:

* original x maps to the canonical class vertex (j,[x]_j);
* a closure vertex (k,E) with k<j maps to the j-class
  representative of any original member of E;
* a closure vertex with k≥j has no j-function value.

The previously checked quotient lemmas show the chosen original
member is immaterial. The newly assigned edge between lower-
and higher-jump closure vertices has metric distance exactly j.
This repairs the functional-domain issue recorded in the
manuscript's review-only audit without altering the paper's text.

The complete class-level condition about every j-class in the
lift and preservation of these functions under embeddings are
separate obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The canonical j-closure function on the entire enlarged
vertex set. Values are partial: j-level and higher-level
closure vertices do not acquire a new j-function value. -/
noncomputable def canonicalCompletedClosureValue {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) :
    (V ⊕ CanonicalJumpTag hpos hS hd) →
      Option (V ⊕ CanonicalJumpTag hpos hS hd)
  | .inl x => some (.inr (canonicalClosureTag hpos hS hd j x))
  | .inr tag =>
      if h : canonicalTagLevel tag < j.val then
        some (.inr (canonicalClosureTag hpos hS hd j
          (canonicalTagRoot tag)))
      else none

@[simp] theorem canonicalCompletedClosureValue_old {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V) :
    canonicalCompletedClosureValue hpos hS hd j (.inl x) =
      some (.inr (canonicalClosureTag hpos hS hd j x)) := rfl

/-- Every smaller-level canonical closure vertex receives the
higher-jump closure function value. -/
theorem canonicalCompletedClosureValue_lower {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S)
    (tag : CanonicalJumpTag hpos hS hd)
    (hlevel : canonicalTagLevel tag < j.val) :
    canonicalCompletedClosureValue hpos hS hd j (.inr tag) =
      some (.inr (canonicalClosureTag hpos hS hd j
        (canonicalTagRoot tag))) := by
  simp [canonicalCompletedClosureValue, hlevel]

/-- At the same or a higher attachment level, the j-function
is undefined on that closure representative. -/
theorem canonicalCompletedClosureValue_ge {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S)
    (tag : CanonicalJumpTag hpos hS hd)
    (hlevel : j.val ≤ canonicalTagLevel tag) :
    canonicalCompletedClosureValue hpos hS hd j (.inr tag) =
      none := by
  simp [canonicalCompletedClosureValue, not_lt.mpr hlevel]

/-- For a smaller-jump tag at level k<j, its higher-jump
function agrees with the j-function of any original
vertex in the same original j-equivalence class. -/
theorem canonicalCompletedClosureValue_lower_class {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S)
    (tag : CanonicalJumpTag hpos hS hd)
    (hlevel : canonicalTagLevel tag < j.val)
    (x : V) (hx : d (canonicalTagRoot tag) x ≤ j.val) :
    canonicalCompletedClosureValue hpos hS hd j (.inr tag) =
      canonicalCompletedClosureValue hpos hS hd j (.inl x) := by
  rw [canonicalCompletedClosureValue_lower hpos hS hd j tag hlevel,
    canonicalCompletedClosureValue_old]
  exact congrArg (fun t : CanonicalJumpTag hpos hS hd =>
      (some (Sum.inr t) : Option (V ⊕ CanonicalJumpTag hpos hS hd)))
    (canonicalClosureTag_eq_of_threshold hpos hS hd j
      (canonicalTagRoot tag) x hx)

/-- The new edge from a lower-jump closure representative
(k,E), k<j, to its enclosing j-class closure vertex has
actual S-metric distance exactly j.

The proof uses the same verified neutral-zero algebra as
the canonical metric: both roots are within j, k≤j,
and j⊕j=j. -/
theorem canonicalCompletedClosureValue_lower_distance {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S)
    (tag : CanonicalJumpTag hpos hS hd)
    (hlevel : canonicalTagLevel tag < j.val) :
    canonicalDistance hpos hS hd
      (.inr tag)
      (.inr (canonicalClosureTag hpos hS hd j
        (canonicalTagRoot tag))) = j.val := by
  let x : V := canonicalTagRoot tag
  let tgt : CanonicalJumpTag hpos hS hd :=
    canonicalClosureTag hpos hS hd j x
  have htgt : canonicalTagLevel tgt = j.val :=
    canonicalClosureTag_level hpos hS hd j x
  have hne : tag ≠ tgt := by
    intro heq
    have hl : canonicalTagLevel tag = j.val := by
      calc
        canonicalTagLevel tag = canonicalTagLevel tgt :=
          congrArg canonicalTagLevel heq
        _ = j.val := htgt
    exact (ne_of_lt hlevel) hl
  have hdroot : d x (canonicalTagRoot tgt) ≤ j.val := by
    rw [hd.symm x (canonicalTagRoot tgt)]
    exact canonicalClosureTag_root_threshold hpos hS hd j x
  have hjmem : j.val ∈ S := j.property.1
  have hjid : sumWithZero S j.val j.val = j.val := by
    rw [sumWithZero_eq_distanceSum hpos hjmem hjmem]
    exact j.property.2.2
  have hxmem : d x (canonicalTagRoot tgt) = 0 ∨
      d x (canonicalTagRoot tgt) ∈ S :=
    metric_value_mem hd x (canonicalTagRoot tgt)
  have hinnerMem :
      sumWithZero S (canonicalTagLevel tag)
        (d x (canonicalTagRoot tgt)) = 0 ∨
      sumWithZero S (canonicalTagLevel tag)
        (d x (canonicalTagRoot tgt)) ∈ S :=
    sumWithZero_mem hpos hS
      (Or.inr (canonicalTagLevel_jump tag).1) hxmem
  have hinner :
      sumWithZero S (canonicalTagLevel tag)
        (d x (canonicalTagRoot tgt)) ≤ j.val := by
    calc
      sumWithZero S (canonicalTagLevel tag)
          (d x (canonicalTagRoot tgt)) ≤
        sumWithZero S j.val
          (d x (canonicalTagRoot tgt)) :=
        sumWithZero_mono_left hpos
          (Or.inr (canonicalTagLevel_jump tag).1)
          (Or.inr hjmem) hxmem (le_of_lt hlevel)
      _ ≤ sumWithZero S j.val j.val :=
        sumWithZero_mono_right hpos (Or.inr hjmem)
          hxmem (Or.inr hjmem) hdroot
      _ = j.val := hjid
  have hupp :
      sumWithZero S
          (sumWithZero S (canonicalTagLevel tag)
            (d x (canonicalTagRoot tgt))) j.val ≤ j.val := by
    calc
      sumWithZero S
          (sumWithZero S (canonicalTagLevel tag)
            (d x (canonicalTagRoot tgt))) j.val ≤
        sumWithZero S j.val j.val :=
        sumWithZero_mono_left hpos hinnerMem
          (Or.inr hjmem) (Or.inr hjmem) hinner
      _ = j.val := hjid
  have hlow : j.val ≤
      sumWithZero S
        (sumWithZero S (canonicalTagLevel tag)
          (d x (canonicalTagRoot tgt))) j.val :=
    le_sumWithZero_right hpos hinnerMem (Or.inr hjmem)
  change canonicalDistance hpos hS hd (.inr tag) (.inr tgt) =
    j.val
  rw [canonicalDistance_new_new hpos hS hd tag tgt hne, htgt]
  exact le_antisymm hupp hlow

end AllThoseRamseyClasses.Applications.MetricSaturation
