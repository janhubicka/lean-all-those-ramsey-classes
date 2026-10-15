import AllThoseRamseyClasses.Applications.MetricJumpSamedist

/-!
# Adjoining one metric closure vertex at an idempotent jump

Let (V,d) be an actual S-metric and j a positive jump, with r a chosen
root. Add one new vertex * with distances

  d(*,x) = j ⊕_S d(r,x),   d(x,*) = d(x,r) ⊕_S j.

Here all sums use the checked neutral-zero extension to S ∪ {0}.
The old distances are left untouched, and the new structure is again
an actual S-metric space. Every original vertex x with d(r,x) ≤ j
has distance exactly j to the new vertex.

This is the local metric extension underlying the paper's closure
imaginaries. The full lift, which adds all jump-equivalence classes,
their inter-level distances, and the correct total order, is separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Rounded addition on its zero-adjoined domain never exceeds real addition. -/
theorem sumWithZero_le_add {S : Set ℝ} (hpos : Positive S)
    {a b : ℝ} (ha : a = 0 ∨ a ∈ S) (hb : b = 0 ∨ b ∈ S) :
    sumWithZero S a b ≤ a + b := by
  rcases ha with hzero | ha
  · subst a
    simp
  rcases hb with hzero | hb
  · subst b
    simp
  · rw [sumWithZero_eq_distanceSum hpos ha hb]
    exact distanceSum_le_add ha (hpos b hb).le

/-- Each input is below its rounded sum; zero is treated as a genuine identity. -/
theorem le_sumWithZero_left {S : Set ℝ} (hpos : Positive S)
    {a b : ℝ} (ha : a = 0 ∨ a ∈ S) (hb : b = 0 ∨ b ∈ S) :
    a ≤ sumWithZero S a b := by
  rcases ha with hzero | ha
  · subst a
    simp only [sumWithZero_zero_left]
    rcases hb with hb0 | hb
    · rw [hb0]
    · exact (hpos b hb).le
  rcases hb with hb0 | hb
  · rw [hb0, sumWithZero_zero_right]
  · rw [sumWithZero_eq_distanceSum hpos ha hb]
    exact left_le_distanceSum ha (hpos b hb).le

theorem le_sumWithZero_right {S : Set ℝ} (hpos : Positive S)
    {a b : ℝ} (ha : a = 0 ∨ a ∈ S) (hb : b = 0 ∨ b ∈ S) :
    b ≤ sumWithZero S a b := by
  rw [sumWithZero_comm S a b]
  exact le_sumWithZero_left hpos hb ha

/-- The initial complete metric is kept on original vertices;
none denotes the newly added closure representative. -/
noncomputable def onePointDistance (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (root : V) (j : ℝ) :
    Option V → Option V → ℝ
  | none, none => 0
  | some x, some y => d x y
  | none, some y => sumWithZero S j (d root y)
  | some x, none => sumWithZero S (d x root) j

@[simp] theorem onePointDistance_old {S : Set ℝ} {V : Type u}
    (d : V → V → ℝ) (root : V) (j : ℝ) (x y : V) :
    onePointDistance S d root j (some x) (some y) = d x y := rfl

@[simp] theorem onePointDistance_new_diag {S : Set ℝ} {V : Type u}
    (d : V → V → ℝ) (root : V) (j : ℝ) :
    onePointDistance S d root j none none = 0 := rfl

/-- The necessary triangle inequality for the new vertex as an endpoint. -/
theorem onePoint_new_triangle {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j) (root y z : V) :
    sumWithZero S j (d root z) ≤
      sumWithZero S j (d root y) + d y z := by
  have hrooty := metric_value_mem hd root y
  have hyz := metric_value_mem hd y z
  have hrootz := metric_value_mem hd root z
  have hmid := sumWithZero_mem hpos hS hrooty hyz
  have htriangle := metric_triangle_rounded hpos hS hd root y z
  calc
    sumWithZero S j (d root z) ≤
        sumWithZero S j (sumWithZero S (d root y) (d y z)) :=
      sumWithZero_mono_right hpos (Or.inr hj.1) hrootz hmid htriangle
    _ = sumWithZero S (sumWithZero S j (d root y)) (d y z) :=
      (sumWithZero_assoc hpos hS hassoc (Or.inr hj.1) hrooty hyz).symm
    _ ≤ sumWithZero S j (d root y) + d y z :=
      sumWithZero_le_add hpos (sumWithZero_mem hpos hS (Or.inr hj.1) hrooty) hyz

/-- The one-point idempotent-star extension is a genuine S-metric.
In particular, the original distances are unchanged, not merely bounded. -/
theorem onePointDistance_metric {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j) (root : V) :
    MetricOn S (onePointDistance S d root j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | none => rfl
    | some x => exact hd.diag x
  · intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => exact False.elim (hxy rfl)
        | some y =>
            exact sumWithZero_mem_of_left_mem hpos hS hj.1
              (metric_value_mem hd root y)
    | some x =>
        cases y with
        | none =>
            exact sumWithZero_mem_of_right_mem hpos hS
              (metric_value_mem hd x root) hj.1
        | some y =>
            exact hd.values x y (by
              intro h
              apply hxy
              exact congrArg some h)
  · intro x y
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            change sumWithZero S j (d root y) =
              sumWithZero S (d y root) j
            calc
              sumWithZero S j (d root y) =
                  sumWithZero S (d root y) j :=
                sumWithZero_comm S j (d root y)
              _ = sumWithZero S (d y root) j := by rw [hd.symm root y]
    | some x =>
        cases y with
        | none =>
            change sumWithZero S (d x root) j =
              sumWithZero S j (d root x)
            calc
              sumWithZero S (d x root) j =
                  sumWithZero S j (d x root) :=
                sumWithZero_comm S (d x root) j
              _ = sumWithZero S j (d root x) := by rw [hd.symm x root]
        | some y => exact hd.symm x y
  · intro a b c
    cases a with
    | none =>
        cases b with
        | none =>
            cases c with
            | none => simp [onePointDistance]
            | some z => simp [onePointDistance]
        | some y =>
            cases c with
            | none =>
                have hleft := le_sumWithZero_left hpos
                  (Or.inr hj.1) (metric_value_mem hd root y)
                have hright := le_sumWithZero_right hpos
                  (metric_value_mem hd y root) (Or.inr hj.1)
                have hjpos := hpos j hj.1
                change 0 ≤ sumWithZero S j (d root y) +
                  sumWithZero S (d y root) j
                linarith
            | some z =>
                exact onePoint_new_triangle hpos hS hassoc hd hj root y z
    | some x =>
        cases b with
        | none =>
            cases c with
            | none => simp [onePointDistance]
            | some z =>
                have hleft := le_sumWithZero_left hpos
                  (metric_value_mem hd x root) (Or.inr hj.1)
                have hright := le_sumWithZero_right hpos
                  (Or.inr hj.1) (metric_value_mem hd root z)
                have htri := hd.triangle x root z
                change d x z ≤ sumWithZero S (d x root) j +
                    sumWithZero S j (d root z)
                linarith
        | some y =>
            cases c with
            | none =>
                have h := onePoint_new_triangle hpos hS hassoc hd hj root y x
                change sumWithZero S (d x root) j ≤
                  d x y + sumWithZero S (d y root) j
                calc
                  sumWithZero S (d x root) j =
                      sumWithZero S j (d root x) := by
                    rw [sumWithZero_comm S (d x root) j, hd.symm x root]
                  _ ≤ sumWithZero S j (d root y) + d y x := h
                  _ = d x y + sumWithZero S (d y root) j := by
                    rw [hd.symm y x, ← hd.symm root y]
                    rw [sumWithZero_comm S j (d root y)]
                    ac_rfl
            | some z => exact hd.triangle x y z

/-- Every vertex of the chosen jump-threshold class is at exactly
distance j from the newly adjoined closure representative. -/
theorem onePointDistance_to_class {S : Set ℝ} {V : Type u}
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j) (root x : V)
    (hx : d root x ≤ j) :
    onePointDistance S d root j none (some x) = j := by
  change sumWithZero S j (d root x) = j
  have hjid : sumWithZero S j j = j := by
    rw [sumWithZero_eq_distanceSum hpos hj.1 hj.1]
    exact hj.2.2
  have hupper := sumWithZero_mono_right hpos
    (Or.inr hj.1) (metric_value_mem hd root x) (Or.inr hj.1) hx
  have hlower := le_sumWithZero_left hpos
    (Or.inr hj.1) (metric_value_mem hd root x)
  rw [hjid] at hupper
  exact le_antisymm hupper hlower


/-- The new closure vertex has distance at most j to precisely the
old j-class. This is stronger than the edge-length assertion in the
definition of the lift: no vertex outside the class enters it. -/
theorem onePointDistance_new_class_iff {S : Set ℝ} {V : Type u}
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j) (root x : V) :
    onePointDistance S d root j none (some x) ≤ j ↔ d root x ≤ j := by
  constructor
  · intro h
    change sumWithZero S j (d root x) ≤ j at h
    have hle := le_sumWithZero_right hpos
      (Or.inr hj.1) (metric_value_mem hd root x)
    exact hle.trans h
  · intro h
    rw [onePointDistance_to_class hpos hd hj root x h]

/-- The length of the two-edge path through any member y of the
chosen class is independent of y: it equals the length through root.
This identifies the added distance with the value selected by the
paper's shortest-path completion, at the level of two-edge walks. -/
theorem onePointDistance_attachment_independent {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j) (root x y : V)
    (hy : d y root ≤ j) :
    sumWithZero S j (d y x) = sumWithZero S j (d root x) := by
  have hyClass : y ∈ thresholdClass d j root := hy
  have hrClass : root ∈ thresholdClass d j root :=
    root_mem_thresholdClass hpos hd (Or.inr hj) root
  have hxClass : x ∈ thresholdClass d 0 x :=
    root_mem_thresholdClass hpos hd (Or.inl rfl) x
  have hh := metric_sandwich_constant_on_parts hpos hS hassoc hd
    j 0 (Or.inr hj) (Or.inl rfl)
    (thresholdClass d j root) (thresholdClass d 0 x)
    (thresholdClass_diameter hpos hS hd (Or.inr hj) root)
    (thresholdClass_diameter hpos hS hd (Or.inl rfl) x)
    y root x x hyClass hrClass hxClass hxClass
  simpa only [sumWithZero_zero_right] using hh


/-- The constructed one-point metric is the greatest allowed
S-metric extension with the prescribed edge from the new vertex
to root: the rounded triangle inequality in any other extension
bounds every new distance by j ⊕ d(root,x). This is the key
universal property of shortest-path completion without quantifying
over all walks. -/
theorem onePointDistance_maximal {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (root : V) (j : ℝ)
    {e : Option V → Option V → ℝ} (he : MetricOn S e)
    (hOld : ∀ x y : V, e (some x) (some y) = d x y)
    (hNewRoot : e none (some root) = j) (x : V) :
    e none (some x) ≤ onePointDistance S d root j none (some x) := by
  have h := metric_triangle_rounded hpos hS he none (some root) (some x)
  rw [hNewRoot, hOld root x] at h
  exact h

end AllThoseRamseyClasses.Applications.MetricSaturation
