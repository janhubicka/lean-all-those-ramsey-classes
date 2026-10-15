import AllThoseRamseyClasses.Applications.MetricZeroExtension
import AllThoseRamseyClasses.Applications.MetricJumpSandwich

/-!
# Metric specialization of the corrected jump-sandwich lemma

The manuscript's Lemma samedist permits jump parameters 0, although
the rounded operation was originally only defined for positive S.
This file gives a faithful S-metric interpretation on S ∪ {0} with
neutral zero. The general sandwich theorem is applied to a *proved*
associative monotone subtype operation and the actual metric triangle
inequality. Its formal equivalence classes use the metric threshold
d(x,root) <= j. The paper's block equivalence is identified with
this relation whenever the stated jump is the maximum of its block.
This includes the trivial zero block and singleton classes.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A finite or infinite S-valued metric, represented without a metric-space
typeclass so the result can be imported by the paper's relational encoding. -/
structure MetricOn (S : Set ℝ) {V : Type u} (d : V → V → ℝ) : Prop where
  diag : ∀ x, d x x = 0
  values : ∀ x y, x ≠ y → d x y ∈ S
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The real metric distance belongs to S ∪ {0}, including the diagonal. -/
theorem metric_value_mem {S : Set ℝ} {V : Type u}
    {d : V → V → ℝ} (hd : MetricOn S d) (x y : V) :
    d x y = 0 ∨ d x y ∈ S := by
  by_cases hxy : x = y
  · subst y
    exact Or.inl (hd.diag x)
  · exact Or.inr (hd.values x y hxy)

/-- The ordinary metric triangle inequality strengthens to the
zero-adjoined rounded-distance triangle inequality. -/
theorem metric_triangle_rounded {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) (x y z : V) :
    d x z ≤ sumWithZero S (d x y) (d y z) := by
  have hxy := metric_value_mem hd x y
  have hyz := metric_value_mem hd y z
  have hxz := metric_value_mem hd x z
  rcases hxy with hxy | hxy
  · rw [hxy, sumWithZero_zero_left]
    linarith [hd.triangle x y z]
  rcases hyz with hyz | hyz
  · rw [hyz, sumWithZero_zero_right]
    linarith [hd.triangle x y z]
  have hxy0 : d x y ≠ 0 := ne_of_gt (hpos _ hxy)
  have hyz0 : d y z ≠ 0 := ne_of_gt (hpos _ hyz)
  rw [show sumWithZero S (d x y) (d y z) =
    distanceSum S (d x y) (d y z) by
      simp [sumWithZero, hxy0, hyz0]]
  rcases hxz with hxz | hxz
  · rw [hxz]
    exact (hpos _ (hS _ hxy _ hyz)).le
  · exact le_distanceSum_of_le_add hxz (hd.triangle x y z)

/-- Distance as an element of the zero-adjoined distance subtype. -/
def metricDistance {S : Set ℝ} {V : Type u}
    {d : V → V → ℝ} (hd : MetricOn S d) (x y : V) :
    WithZero S := ⟨d x y, metric_value_mem hd x y⟩

theorem metricDistance_triangle {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) (x y z : V) :
    metricDistance hd x z ≤
      zeroOp S hpos hS (metricDistance hd x y) (metricDistance hd y z) :=
  metric_triangle_rounded hpos hS hd x y z

/-- A zero or positive jump is a nonnegative distance threshold. -/
theorem threshold_nonneg {S : Set ℝ} (hpos : Positive S)
    {j : ℝ} (hj : j = 0 ∨ Jump S j) : 0 ≤ j := by
  rcases hj with rfl | hj
  · exact le_refl _
  · exact (hpos j hj.1).le

/-- One-sided jumps are enough to make the threshold relation transitive;
there is no need to assume that the ambient set of distances is finite. -/
theorem metric_jump_threshold_trans {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : j = 0 ∨ Jump S j)
    (x y z : V) (hxy : d x y ≤ j) (hyz : d y z ≤ j) :
    d x z ≤ j := by
  have hjmem : j = 0 ∨ j ∈ S :=
    hj.elim Or.inl (fun h => Or.inr h.1)
  calc
    d x z ≤ sumWithZero S (d x y) (d y z) :=
      metric_triangle_rounded hpos hS hd x y z
    _ ≤ sumWithZero S j (d y z) :=
      sumWithZero_mono_left hpos (metric_value_mem hd x y)
        hjmem (metric_value_mem hd y z) hxy
    _ ≤ sumWithZero S j j :=
      sumWithZero_mono_right hpos hjmem (metric_value_mem hd y z)
        hjmem hyz
    _ = j := by
      have h := congrArg Subtype.val
        (threshold_idempotent hpos hS j hj)
      exact h

/-- The threshold equivalence class rooted at a vertex. -/
def thresholdClass {V : Type u} (d : V → V → ℝ)
    (j : ℝ) (root : V) : Set V :=
  {x | d x root ≤ j}

/-- A threshold class of a jump (or zero) has diameter at most j. -/
theorem thresholdClass_diameter {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : j = 0 ∨ Jump S j) (root : V) :
    ∀ x ∈ thresholdClass d j root,
      ∀ y ∈ thresholdClass d j root, d x y ≤ j := by
  intro x hx y hy
  exact metric_jump_threshold_trans hpos hS hd hj x root y hx
    (by rw [hd.symm root y]; exact hy)

/-- Specialization of the reusable idempotent sandwich theorem to
actual S-metrics. Both thresholds may be zero. -/
theorem metric_sandwich_constant_on_parts {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (p q : ℝ) (hp : p = 0 ∨ Jump S p)
    (hq : q = 0 ∨ Jump S q)
    (E F : Set V)
    (hE : ∀ x ∈ E, ∀ y ∈ E, d x y ≤ p)
    (hF : ∀ x ∈ F, ∀ y ∈ F, d x y ≤ q)
    (u u' v v' : V) (hu : u ∈ E) (hu' : u' ∈ E)
    (hv : v ∈ F) (hv' : v' ∈ F) :
    sumWithZero S (sumWithZero S p (d u v)) q =
      sumWithZero S (sumWithZero S p (d u' v')) q := by
  let op := zeroOp S hpos hS
  let d0 := metricDistance hd
  let p0 := threshold S p hp
  let q0 := threshold S q hq
  have hPartE : ∀ x ∈ E, ∀ y ∈ E, d0 x y ≤ p0 := by
    intro x hx y hy
    exact hE x hx y hy
  have hPartF : ∀ x ∈ F, ∀ y ∈ F, d0 x y ≤ q0 := by
    intro x hx y hy
    exact hF x hx y hy
  have hresult := MetricJump.sandwich_constant_on_parts
    op
    (zeroOp_assoc hpos hS hassoc)
    (fun _ _ _ h => zeroOp_mono_left hpos hS h)
    (fun _ _ _ h => zeroOp_mono_right hpos hS h)
    d0
    (metricDistance_triangle hpos hS hd)
    p0 q0 (threshold_idempotent hpos hS p hp)
    (threshold_idempotent hpos hS q hq)
    E F hPartE hPartF u u' v v' hu hu' hv hv'
  exact congrArg Subtype.val hresult

/-- The metric class rooted at a jump is nonempty: the root belongs. -/
theorem root_mem_thresholdClass {S : Set ℝ} {V : Type u}
    (hpos : Positive S) {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : j = 0 ∨ Jump S j) (root : V) :
    root ∈ thresholdClass d j root := by
  change d root root ≤ j
  rw [hd.diag root]
  exact threshold_nonneg hpos hj

/-- A corrected S-metric version of the paper's Lemma samedist
for the equivalence classes at two jump thresholds, including zero.
Disjointness of the classes is not needed for the invariance. -/
theorem metric_samedist_threshold_classes {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (p q : ℝ) (hp : p = 0 ∨ Jump S p)
    (hq : q = 0 ∨ Jump S q)
    (root1 root2 : V) :
    ∃ ell : ℝ,
      ∀ u ∈ thresholdClass d p root1,
        ∀ v ∈ thresholdClass d q root2,
          sumWithZero S (sumWithZero S p (d u v)) q = ell := by
  refine ⟨sumWithZero S (sumWithZero S p (d root1 root2)) q, ?_⟩
  intro u hu v hv
  exact (metric_sandwich_constant_on_parts hpos hS hassoc hd
    p q hp hq
    (thresholdClass d p root1) (thresholdClass d q root2)
    (thresholdClass_diameter hpos hS hd hp root1)
    (thresholdClass_diameter hpos hS hd hq root2)
    u root1 v root2 hu (root_mem_thresholdClass hpos hd hp root1)
    hv (root_mem_thresholdClass hpos hd hq root2))

/-- A block with largest member j defines exactly the same metric class
as the distance threshold j. Includes B={0}, j=0. -/
theorem blockClass_eq_thresholdClass {V : Type u}
    (d : V → V → ℝ) (B : Set ℝ) (j : ℝ)
    (hjB : j ∈ B) (hjmax : ∀ b ∈ B, b ≤ j) (root : V) :
    {x : V | ∃ b ∈ B, d x root ≤ b} =
      thresholdClass d j root := by
  ext x
  constructor
  · rintro ⟨b, hb, hxb⟩
    exact hxb.trans (hjmax b hb)
  · intro hx
    exact ⟨j, hjB, hx⟩

/-- Exact corrected block-class statement using only the published
fact that j=max(B_j) (or the trivial B_0={0}); it is valid even for
infinite S provided the two blocks have maxima. The original four-point
argument is replaced by neutral-zero sandwiching. -/
theorem metric_samedist_bounded_blocks {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (B1 B2 : Set ℝ) (p q : ℝ)
    (hp : p = 0 ∨ Jump S p) (hq : q = 0 ∨ Jump S q)
    (hpB : p ∈ B1) (hpmax : ∀ b ∈ B1, b ≤ p)
    (hqB : q ∈ B2) (hqmax : ∀ b ∈ B2, b ≤ q)
    (root1 root2 : V) :
    ∃ ell : ℝ,
      ∀ u : V, (∃ b ∈ B1, d u root1 ≤ b) →
        ∀ v : V, (∃ b ∈ B2, d v root2 ≤ b) →
          sumWithZero S (sumWithZero S p (d u v)) q = ell := by
  obtain ⟨ell, hconstant⟩ :=
    metric_samedist_threshold_classes hpos hS hassoc hd
      p q hp hq root1 root2
  refine ⟨ell, ?_⟩
  intro u hu v hv
  apply hconstant u
  · rw [← blockClass_eq_thresholdClass d B1 p hpB hpmax root1]
    exact hu
  · rw [← blockClass_eq_thresholdClass d B2 q hqB hqmax root2]
    exact hv

end AllThoseRamseyClasses.Applications.MetricSaturation
