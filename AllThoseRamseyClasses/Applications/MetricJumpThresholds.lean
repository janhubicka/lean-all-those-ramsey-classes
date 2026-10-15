import AllThoseRamseyClasses.Applications.MetricFourValues

/-!
# Jump thresholds under finite capped distance reduction

The paper defines a jump j in S by requiring that j is not the maximum
of S and that no element of S lies in (j, 2*j]. For positive distances
with well-defined rounded sums, this is equivalent to the proper
idempotency condition distanceSum S j j = j.

For a finite T obtained by closing distances below a cap m, this file
proves two exact transfer statements:

* Every proper jump of T is a jump of S.
* Below any ambient jump j < m, provided T has a distance <= j, the
  largest such distance t is a proper jump of T, and T-distance
  comparisons with j and t are identical.

This is algebraic threshold transport, not yet the full class-level
Ramsey theorem or the paper's block-convexity representation.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Proper idempotent jump of the rounded distance semigroup.
For positive well-defined S this is the paper's jump definition. -/
def Jump (S : Set ℝ) (j : ℝ) : Prop :=
  j ∈ S ∧ (∃ b ∈ S, j < b) ∧ distanceSum S j j = j

/-- Exactly the manuscript's gap criterion, with no finiteness or
topological closedness assumption. -/
theorem jump_iff_gap {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) (j : ℝ) :
    Jump S j ↔
      j ∈ S ∧ (∃ b ∈ S, j < b) ∧
        ∀ b ∈ S, j < b → 2 * j < b := by
  constructor
  · rintro ⟨hj, hproper, hid⟩
    refine ⟨hj, hproper, ?_⟩
    intro b hb hjb
    by_contra hn
    have hbj : b ≤ j + j := by linarith
    have hle := le_distanceSum_of_le_add hb hbj
    rw [hid] at hle
    linarith
  · rintro ⟨hj, hproper, hgap⟩
    have hmem := hS j hj j hj
    have hlow := left_le_distanceSum hj (hpos j hj).le
    have hupp := distanceSum_le_add hj (hpos j hj).le
    refine ⟨hj, hproper, le_antisymm ?_ hlow⟩
    by_contra hn
    have hlt : j < distanceSum S j j := lt_of_not_ge hn
    have hg := hgap _ hmem hlt
    linarith

/-- A nonempty finite subset of the allowed distances below j has
a greatest element, without assuming any density or closedness. -/
theorem exists_max_below {T : Set ℝ} (hT : T.Finite) {j : ℝ}
    (hne : ∃ s ∈ T, s ≤ j) :
    ∃ t ∈ T, t ≤ j ∧ ∀ s ∈ T, s ≤ j → s ≤ t := by
  let U : Set ℝ := {s | s ∈ T ∧ s ≤ j}
  have hU : U.Finite := hT.subset (by intro s hs; exact hs.1)
  obtain ⟨a, ha, haj⟩ := hne
  let F : Finset ℝ := hU.toFinset
  have hF : F.Nonempty :=
    ⟨a, hU.mem_toFinset.mpr ⟨ha, haj⟩⟩
  let t : ℝ := F.max' hF
  have htU : t ∈ U :=
    hU.mem_toFinset.mp (Finset.max'_mem F hF)
  refine ⟨t, htU.1, htU.2, ?_⟩
  intro s hs hsj
  exact Finset.le_max' F s (hU.mem_toFinset.mpr ⟨hs, hsj⟩)

/-- Every T-jump strictly below the cap is already an S-jump.
The cap may be in T but T need not include all ambient distances. -/
theorem jump_of_restricted_jump {S T : Set ℝ} {m t : ℝ}
    (hpos : Positive S) (hTS : T ⊆ S)
    (hbound : ∀ s ∈ T, s ≤ m)
    (hclosed : ∀ a ∈ T, ∀ b ∈ T, cappedSum S m a b ∈ T)
    (hjump : Jump T t) : Jump S t := by
  obtain ⟨ht, ⟨u, hu, htu⟩, hidT⟩ := hjump
  have htm : t < m := lt_of_lt_of_le htu (hbound u hu)
  have heq : cappedSum S m t t = t := by
    calc
      cappedSum S m t t = distanceSum T t t :=
        (distanceSum_subset_eq_capped hpos hTS hbound hclosed ht ht).symm
      _ = t := hidT
  have hidS : distanceSum S t t = t := by
    rcases le_total m (distanceSum S t t) with hmle | hdm
    · have hmeq : m = t := by
        simpa only [cappedSum, min_eq_left hmle] using heq
      exact False.elim ((ne_of_gt htm) hmeq)
    · simpa only [cappedSum, min_eq_right hdm] using heq
  exact ⟨hTS ht, ⟨u, hTS hu, htu⟩, hidS⟩

/-- If an ambient jump j is below m, any finite capped-closed T
containing a distance at most j has a *proper* jump t with the same
threshold relation on T. The proof uses the largest distance of T
below j and its squared capped sum. -/
theorem exists_restricted_jump_below {S T : Set ℝ} {m j : ℝ}
    (hpos : Positive S) (hT : T.Finite) (hTS : T ⊆ S)
    (hm : m ∈ T) (hbound : ∀ s ∈ T, s ≤ m)
    (hclosed : ∀ a ∈ T, ∀ b ∈ T, cappedSum S m a b ∈ T)
    (hjump : Jump S j) (hjm : j < m)
    (hne : ∃ s ∈ T, s ≤ j) :
    ∃ t : ℝ, Jump T t ∧
      ∀ s ∈ T, (s ≤ j ↔ s ≤ t) := by
  obtain ⟨t, ht, htj, hmax⟩ := exists_max_below hT hne
  have hmono : distanceSum S t t ≤ distanceSum S j j := by
    calc
      distanceSum S t t ≤ distanceSum S t j :=
        distanceSum_mono_right (hTS ht) (hpos t (hTS ht)).le htj
      _ = distanceSum S j t := distanceSum_comm S t j
      _ ≤ distanceSum S j j :=
        distanceSum_mono_right hjump.1 (hpos t (hTS ht)).le htj
  have hsum : cappedSum S m t t ≤ j := by
    calc
      cappedSum S m t t ≤ distanceSum S t t := min_le_right _ _
      _ ≤ distanceSum S j j := hmono
      _ = j := hjump.2.2
  have hsum_mem := hclosed t ht t ht
  have hsum_le_t : cappedSum S m t t ≤ t :=
    hmax _ hsum_mem hsum
  have ht_le_sum : t ≤ cappedSum S m t t :=
    le_cappedSum (hTS ht) (hbound t ht)
      (by linarith [hpos t (hTS ht)])
  have hidT : distanceSum T t t = t := by
    rw [distanceSum_subset_eq_capped hpos hTS hbound hclosed ht ht]
    exact le_antisymm hsum_le_t ht_le_sum
  refine ⟨t, ⟨ht, ⟨m, hm, lt_of_le_of_lt htj hjm⟩, hidT⟩, ?_⟩
  intro s hs
  exact ⟨fun hsj => hmax s hs hsj, fun hst => hst.trans htj⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
