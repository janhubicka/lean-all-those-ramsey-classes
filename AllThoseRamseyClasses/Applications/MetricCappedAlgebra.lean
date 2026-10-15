import AllThoseRamseyClasses.Applications.MetricSaturation

/-!
# Algebra of capped rounded distance sums

These lemmas establish the actual scalar hypotheses needed for the metric
finite-generation step. Capped associativity is derived from associativity
of the original rounded sum. A cap-closed subset inherits its own rounded
sum exactly, not merely a different associative operation on the same set.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- All allowed distances are strictly positive. -/
def Positive (S : Set ℝ) : Prop := ∀ s ∈ S, 0 < s

/-- Associativity only on the allowed operands, not on all real numbers. -/
def AssociativeOn (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
    distanceSum S (distanceSum S a b) c = distanceSum S a (distanceSum S b c)

/-- Rounded sums never exceed the ordinary sum when the candidate set is nonempty. -/
theorem distanceSum_le_add {S : Set ℝ} {a b : ℝ}
    (ha : a ∈ S) (hb : 0 ≤ b) : distanceSum S a b ≤ a + b := by
  have hne : {s : ℝ | s ∈ S ∧ s ≤ a + b}.Nonempty :=
    ⟨a, ha, by linarith⟩
  exact csSup_le hne (fun _ hs => hs.2)

/-- Adding a nonnegative operand does not decrease an allowed distance. -/
theorem left_le_distanceSum {S : Set ℝ} {a b : ℝ}
    (ha : a ∈ S) (hb : 0 ≤ b) : a ≤ distanceSum S a b := by
  exact le_csSup ⟨a + b, fun _ hs => hs.2⟩ ⟨ha, by linarith⟩

/-- Commutativity follows directly from the defining ordinary sum. -/
theorem distanceSum_comm (S : Set ℝ) (a b : ℝ) :
    distanceSum S a b = distanceSum S b a := by
  simp only [distanceSum, add_comm a b]

/-- Capping preserves commutativity. -/
theorem cappedSum_comm (S : Set ℝ) (m a b : ℝ) :
    cappedSum S m a b = cappedSum S m b a := by
  unfold cappedSum
  rw [distanceSum_comm S a b]

/-- An inner cap can be moved to the outside of a rounded sum. -/
theorem cappedSum_left_cap {S : Set ℝ} {m a b c : ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hm : m ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    cappedSum S m (cappedSum S m a b) c =
      min m (distanceSum S (distanceSum S a b) c) := by
  unfold cappedSum
  by_cases hab : distanceSum S a b ≤ m
  · rw [min_eq_right hab]
  · have hmab : m ≤ distanceSum S a b := le_of_lt (lt_of_not_ge hab)
    have hmc := left_le_distanceSum hm (hpos c hc).le
    have habc := left_le_distanceSum (hS a ha b hb) (hpos c hc).le
    rw [min_eq_left hmab, min_eq_left hmc, min_eq_left (hmab.trans habc)]

/-- The right-hand version of moving an inner cap outside. -/
theorem cappedSum_right_cap {S : Set ℝ} {m a b c : ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hm : m ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    cappedSum S m a (cappedSum S m b c) =
      min m (distanceSum S a (distanceSum S b c)) := by
  rw [cappedSum_comm S m a (cappedSum S m b c),
    cappedSum_left_cap hpos hS hm hb hc ha,
    distanceSum_comm S (distanceSum S b c) a]

/-- Actual capped associativity, derived rather than assumed. -/
theorem cappedSum_assoc {S : Set ℝ} {m a b c : ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S)
    (hm : m ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    cappedSum S m (cappedSum S m a b) c =
      cappedSum S m a (cappedSum S m b c) := by
  rw [cappedSum_left_cap hpos hS hm ha hb hc,
    cappedSum_right_cap hpos hS hm ha hb hc, hassoc a ha b hb c hc]

/-- A subset closed under the capped operation inherits precisely its own
rounded operation. Finiteness and closedness in the real topology are unnecessary. -/
theorem distanceSum_subset_eq_capped {S T : Set ℝ} {m a b : ℝ}
    (hpos : Positive S) (hTS : T ⊆ S) (hbound : ∀ t ∈ T, t ≤ m)
    (hclosed : ∀ x ∈ T, ∀ y ∈ T, cappedSum S m x y ∈ T)
    (ha : a ∈ T) (hb : b ∈ T) :
    distanceSum T a b = cappedSum S m a b := by
  have hne : {s : ℝ | s ∈ T ∧ s ≤ a + b}.Nonempty :=
    ⟨a, ha, by linarith [hpos b (hTS hb)]⟩
  apply le_antisymm
  · apply csSup_le hne
    intro t ht
    exact le_cappedSum (hTS ht.1) (hbound t ht.1) ht.2
  · have hle : cappedSum S m a b ≤ a + b :=
      (min_le_right _ _).trans (distanceSum_le_add (hTS ha) (hpos b (hTS hb)).le)
    exact le_csSup ⟨a + b, fun _ hs => hs.2⟩ ⟨hclosed a ha b hb, hle⟩

/-- Well-definedness transfers to a cap-closed subset by the exact operation identity. -/
theorem wellDefined_subset {S T : Set ℝ} {m : ℝ}
    (hpos : Positive S) (hTS : T ⊆ S) (hbound : ∀ t ∈ T, t ≤ m)
    (hclosed : ∀ x ∈ T, ∀ y ∈ T, cappedSum S m x y ∈ T) :
    WellDefined T := by
  intro a ha b hb
  rw [distanceSum_subset_eq_capped hpos hTS hbound hclosed ha hb]
  exact hclosed a ha b hb

/-- The inherited rounded operation is associative, not just the ambient one. -/
theorem associativeOn_subset {S T : Set ℝ} {m : ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S)
    (hm : m ∈ S) (hTS : T ⊆ S) (hbound : ∀ t ∈ T, t ≤ m)
    (hclosed : ∀ x ∈ T, ∀ y ∈ T, cappedSum S m x y ∈ T) :
    AssociativeOn T := by
  have hT := wellDefined_subset hpos hTS hbound hclosed
  have heq : ∀ {a b : ℝ}, a ∈ T → b ∈ T →
      distanceSum T a b = cappedSum S m a b :=
    fun ha hb => distanceSum_subset_eq_capped hpos hTS hbound hclosed ha hb
  intro a ha b hb c hc
  rw [heq (hT a ha b hb) hc, heq ha (hT b hb c hc), heq ha hb, heq hb hc]
  exact cappedSum_assoc hpos hS hassoc hm (hTS ha) (hTS hb) (hTS hc)

end AllThoseRamseyClasses.Applications.MetricSaturation
