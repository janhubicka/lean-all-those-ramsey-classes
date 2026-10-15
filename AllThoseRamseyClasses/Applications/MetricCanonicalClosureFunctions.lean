import AllThoseRamseyClasses.Applications.MetricCanonicalDistance

/-!
# Canonical jump-closure functions on original metric vertices

For every positive proper jump level j and original vertex x,
the paper's lifted language has a closure vertex representing the
equivalence class [x]_j. The canonical tag type already encodes this
vertex uniquely, so we define its closure function directly by
taking the quotient class of x, without choosing an arbitrary root.

The checked canonical metric then puts this closure vertex at exactly
distance j from x and from every other member of its class.
These are metric/function axioms of the paper's proposed lift,
not yet its extended convex linear order or Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The unique canonical closure vertex attached to x at a positive
proper jump level j. The output is a dependent (jump,class) tag. -/
noncomputable def canonicalClosureTag {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V) :
    CanonicalJumpTag hpos hS hd :=
  ⟨j, Quotient.mk
    (jumpSetoid hpos hS hd j.val (Or.inr j.property)) x⟩

@[simp] theorem canonicalClosureTag_level {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V) :
    canonicalTagLevel (canonicalClosureTag hpos hS hd j x) = j.val := rfl

/-- The defining class of the newly attached closure vertex really
is the original j-threshold quotient class of x. -/
theorem canonicalClosureTag_class {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V) :
    (canonicalClosureTag hpos hS hd j x).2 =
      Quotient.mk
        (jumpSetoid hpos hS hd j.val (Or.inr j.property)) x := rfl

/-- A jump-closure function is constant on every one of its
equivalence classes, as required by the functional lift. -/
theorem canonicalClosureTag_eq_of_threshold {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x y : V)
    (hxy : d x y ≤ j.val) :
    canonicalClosureTag hpos hS hd j x =
      canonicalClosureTag hpos hS hd j y := by
  exact congrArg (fun q : JumpClasses hpos hS hd j.val
    (Or.inr j.property) => (⟨j, q⟩ : CanonicalJumpTag hpos hS hd))
    (Quotient.sound hxy)

/-- The chosen Quotient.out representative of the canonical
closure tag is in the same j-class as the original vertex x. -/
theorem canonicalClosureTag_root_threshold {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V) :
    d (canonicalTagRoot (canonicalClosureTag hpos hS hd j x)) x ≤
      j.val := by
  have hclass :=
    canonicalTagRoot_class (canonicalClosureTag hpos hS hd j x)
  change Quotient.mk
    (jumpSetoid hpos hS hd j.val (Or.inr j.property))
      (canonicalTagRoot (canonicalClosureTag hpos hS hd j x)) =
    Quotient.mk (jumpSetoid hpos hS hd j.val
      (Or.inr j.property)) x at hclass
  exact Quotient.exact hclass

/-- The canonical metric places the j-closure vertex of x
at exactly distance j from its source x. -/
theorem canonicalClosureTag_distance {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V) :
    canonicalDistance hpos hS hd
        (.inr (canonicalClosureTag hpos hS hd j x))
        (.inl x) = j.val := by
  rw [canonicalDistance_new_old]
  have hjump : Jump S j.val := j.property
  have hjid : sumWithZero S j.val j.val = j.val := by
    rw [sumWithZero_eq_distanceSum hpos hjump.1 hjump.1]
    exact hjump.2.2
  have hupper := sumWithZero_mono_right hpos
    (Or.inr hjump.1)
    (metric_value_mem hd
      (canonicalTagRoot (canonicalClosureTag hpos hS hd j x)) x)
    (Or.inr hjump.1)
    (canonicalClosureTag_root_threshold hpos hS hd j x)
  have hlower := le_sumWithZero_left hpos
    (Or.inr hjump.1)
    (metric_value_mem hd
      (canonicalTagRoot (canonicalClosureTag hpos hS hd j x)) x)
  rw [canonicalClosureTag_level, hjid] at hupper
  rw [canonicalClosureTag_level] at hlower
  exact le_antisymm hupper hlower

/-- Every two original vertices in one j-class have the same
canonical closure vertex at exact distance j from both. -/
theorem canonicalClosureTag_class_distance {S : Set ℝ}
    {V : Type u} (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x y : V)
    (hxy : d x y ≤ j.val) :
    canonicalDistance hpos hS hd
      (.inr (canonicalClosureTag hpos hS hd j x)) (.inl y) =
        j.val := by
  rw [canonicalClosureTag_eq_of_threshold hpos hS hd j x y hxy]
  exact canonicalClosureTag_distance hpos hS hd j y

end AllThoseRamseyClasses.Applications.MetricSaturation
