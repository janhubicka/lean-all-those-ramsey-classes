import AllThoseRamseyClasses.Applications.MetricJumpThresholds
import Mathlib.Tactic

/-!
# Adjoin a neutral zero to the rounded distance semigroup

The manuscript uses positive distance sets S, but distances on the
diagonal and both jump parameters in Lemma samedist can be zero.
This file defines the operation on the *actual subtype* S ∪ {0},
proves closure, associativity and monotonicity rather than assuming
them, and identifies the original positive jumps as idempotents.

This is scalar algebra. The metric-space specialization is in
MetricJumpSamedist.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Positive allowed distances together with the zero diagonal. -/
abbrev WithZero (S : Set ℝ) := {x : ℝ // x = 0 ∨ x ∈ S}

/-- The manuscript's rounded sum, with zero explicitly neutral. -/
noncomputable def sumWithZero (S : Set ℝ) (a b : ℝ) : ℝ :=
  if a = 0 then b else if b = 0 then a else distanceSum S a b

@[simp] theorem sumWithZero_zero_left (S : Set ℝ) (b : ℝ) :
    sumWithZero S 0 b = b := by
  simp [sumWithZero]

@[simp] theorem sumWithZero_zero_right (S : Set ℝ) (a : ℝ) :
    sumWithZero S a 0 = a := by
  by_cases ha : a = 0
  · subst a
    simp
  · simp [sumWithZero, ha]

theorem sumWithZero_comm (S : Set ℝ) (a b : ℝ) :
    sumWithZero S a b = sumWithZero S b a := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  · simp [sumWithZero, ha, hb, distanceSum_comm S a b]

/-- The extended operation preserves S ∪ {0}. -/
theorem sumWithZero_mem {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) {a b : ℝ}
    (ha : a = 0 ∨ a ∈ S) (hb : b = 0 ∨ b ∈ S) :
    sumWithZero S a b = 0 ∨ sumWithZero S a b ∈ S := by
  rcases ha with rfl | ha
  · simpa using hb
  rcases hb with rfl | hb
  · simpa using (Or.inr ha : a = 0 ∨ a ∈ S)
  · have ha0 : a ≠ 0 := ne_of_gt (hpos a ha)
    have hb0 : b ≠ 0 := ne_of_gt (hpos b hb)
    exact Or.inr (by simpa [sumWithZero, ha0, hb0] using hS a ha b hb)

/-- The neutral-zero extension is associative on its actual domain. -/
theorem sumWithZero_assoc {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S) {a b c : ℝ}
    (ha : a = 0 ∨ a ∈ S) (hb : b = 0 ∨ b ∈ S)
    (hc : c = 0 ∨ c ∈ S) :
    sumWithZero S (sumWithZero S a b) c =
      sumWithZero S a (sumWithZero S b c) := by
  rcases ha with rfl | ha
  · simp
  rcases hb with rfl | hb
  · simp
  rcases hc with rfl | hc
  · simp
  have ha0 : a ≠ 0 := ne_of_gt (hpos a ha)
  have hb0 : b ≠ 0 := ne_of_gt (hpos b hb)
  have hc0 : c ≠ 0 := ne_of_gt (hpos c hc)
  have hab : distanceSum S a b ∈ S := hS a ha b hb
  have hbc : distanceSum S b c ∈ S := hS b hb c hc
  have hab0 : distanceSum S a b ≠ 0 := ne_of_gt (hpos _ hab)
  have hbc0 : distanceSum S b c ≠ 0 := ne_of_gt (hpos _ hbc)
  simpa only [sumWithZero, if_neg ha0, if_neg hb0, if_neg hc0,
    if_neg hab0, if_neg hbc0] using hassoc a ha b hb c hc

/-- Monotonicity on the ordered zero-adjoined distance domain. -/
theorem sumWithZero_mono_right {S : Set ℝ} (hpos : Positive S)
    {a b c : ℝ} (ha : a = 0 ∨ a ∈ S)
    (hb : b = 0 ∨ b ∈ S) (hc : c = 0 ∨ c ∈ S)
    (hbc : b ≤ c) :
    sumWithZero S a b ≤ sumWithZero S a c := by
  rcases ha with rfl | ha
  · simpa using hbc
  have ha0 : a ≠ 0 := ne_of_gt (hpos a ha)
  rcases hb with rfl | hb
  · rcases hc with rfl | hc
    · exact le_refl _
    · have hc0 : c ≠ 0 := ne_of_gt (hpos c hc)
      simpa [sumWithZero, ha0, hc0] using
        left_le_distanceSum ha (hpos c hc).le
  · have hb0 : b ≠ 0 := ne_of_gt (hpos b hb)
    rcases hc with rfl | hc
    · exact False.elim (not_lt_of_ge hbc (hpos b hb))
    · have hc0 : c ≠ 0 := ne_of_gt (hpos c hc)
      simpa [sumWithZero, ha0, hb0, hc0] using
        distanceSum_mono_right ha (hpos b hb).le hbc

theorem sumWithZero_mono_left {S : Set ℝ} (hpos : Positive S)
    {a b c : ℝ} (ha : a = 0 ∨ a ∈ S)
    (hb : b = 0 ∨ b ∈ S) (hc : c = 0 ∨ c ∈ S)
    (hab : a ≤ b) :
    sumWithZero S a c ≤ sumWithZero S b c := by
  rw [sumWithZero_comm S a c, sumWithZero_comm S b c]
  exact sumWithZero_mono_right hpos hc ha hb hab

/-- A genuine subtype operation; no values outside S ∪ {0} are used. -/
noncomputable def zeroOp (S : Set ℝ) (hpos : Positive S)
    (hS : WellDefined S) (a b : WithZero S) : WithZero S :=
  ⟨sumWithZero S a.val b.val,
    sumWithZero_mem hpos hS a.property b.property⟩

theorem zeroOp_assoc {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) (hassoc : AssociativeOn S)
    (a b c : WithZero S) :
    zeroOp S hpos hS (zeroOp S hpos hS a b) c =
      zeroOp S hpos hS a (zeroOp S hpos hS b c) := by
  apply Subtype.ext
  exact sumWithZero_assoc hpos hS hassoc a.property b.property c.property

theorem zeroOp_mono_right {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) {a b c : WithZero S}
    (hab : a ≤ b) :
    zeroOp S hpos hS c a ≤ zeroOp S hpos hS c b :=
  sumWithZero_mono_right hpos c.property a.property b.property hab

theorem zeroOp_mono_left {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) {a b c : WithZero S}
    (hab : a ≤ b) :
    zeroOp S hpos hS a c ≤ zeroOp S hpos hS b c :=
  sumWithZero_mono_left hpos a.property b.property c.property hab

/-- A threshold is either zero or a proper jump of S. -/
def threshold (S : Set ℝ) (j : ℝ) (hj : j = 0 ∨ Jump S j) :
    WithZero S :=
  ⟨j, hj.elim Or.inl (fun h => Or.inr h.1)⟩

theorem threshold_idempotent {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) :
    zeroOp S hpos hS (threshold S j hj) (threshold S j hj) =
      threshold S j hj := by
  apply Subtype.ext
  change sumWithZero S j j = j
  rcases hj with hzero | hJ
  · subst j
    simp
  · have hj0 : j ≠ 0 := ne_of_gt (hpos j hJ.1)
    simp [sumWithZero, hj0, hJ.2.2]


/-- When the right argument is a positive allowed distance, the
zero-extended operation itself lies in S (rather than merely S ∪ {0}). -/
theorem sumWithZero_mem_of_right_mem {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {a b : ℝ} (ha : a = 0 ∨ a ∈ S) (hb : b ∈ S) :
    sumWithZero S a b ∈ S := by
  rcases ha with hzero | ha
  · rw [hzero, sumWithZero_zero_left]
    exact hb
  · have ha0 : a ≠ 0 := ne_of_gt (hpos a ha)
    have hb0 : b ≠ 0 := ne_of_gt (hpos b hb)
    simpa [sumWithZero, ha0, hb0] using hS a ha b hb

/-- Symmetric preservation of genuine positive distances. -/
theorem sumWithZero_mem_of_left_mem {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {a b : ℝ} (ha : a ∈ S) (hb : b = 0 ∨ b ∈ S) :
    sumWithZero S a b ∈ S := by
  rw [sumWithZero_comm S a b]
  exact sumWithZero_mem_of_right_mem hpos hS hb ha

/-- On positive operands the neutral-zero extension agrees with the
original rounded-distance sum exactly. -/
theorem sumWithZero_eq_distanceSum {S : Set ℝ} (hpos : Positive S)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    sumWithZero S a b = distanceSum S a b := by
  have ha0 : a ≠ 0 := ne_of_gt (hpos a ha)
  have hb0 : b ≠ 0 := ne_of_gt (hpos b hb)
  simp [sumWithZero, ha0, hb0]

end AllThoseRamseyClasses.Applications.MetricSaturation
