import AllThoseRamseyClasses.Applications.MetricJumpThresholds

/-!
# Convexity at jump thresholds is invariant under finite distance reduction

For a linearly ordered vertex set with distances in T (and zero on the
diagonal), the statement that every interval between vertices at
distance <= j stays at distance <= j is identical for the jump
thresholds of S and T when T is finite and closed under the capped
ambient operation.

Only the jump-threshold formulation is used; the manuscript's block
equivalences and full Ramsey-class statement still need their own
representation-level bridges. In particular this file does not
identify a closure-vertex construction or prove a metric Ramsey arrow.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The relation d(x,z) <= j has convex classes in a linearly ordered
vertex set, expressed as an interval condition rather than an abstract
equivalence relation. -/
def ConvexAt {V : Type u} [LinearOrder V]
    (d : V → V → ℝ) (j : ℝ) : Prop :=
  ∀ x y z : V, x ≤ y → y ≤ z → d x z ≤ j →
    d x y ≤ j ∧ d y z ≤ j

/-- Convexity at every proper jump threshold in the ambient set. -/
def JumpConvex {V : Type u} [LinearOrder V]
    (S : Set ℝ) (d : V → V → ℝ) : Prop :=
  ∀ j : ℝ, Jump S j → ConvexAt d j

/-- Two thresholds agreeing on all positive distances in T give the
same convexity condition when the diagonal is zero. -/
theorem convexAt_iff_same_threshold {V : Type u} [LinearOrder V]
    {T : Set ℝ} (d : V → V → ℝ)
    (hdiag : ∀ x, d x x = 0)
    (hrange : ∀ x y, x ≠ y → d x y ∈ T)
    {j t : ℝ} (hjpos : 0 ≤ j) (htpos : 0 ≤ t)
    (hsame : ∀ s ∈ T, (s ≤ j ↔ s ≤ t)) :
    ConvexAt d j ↔ ConvexAt d t := by
  have heq : ∀ x y : V, d x y ≤ j ↔ d x y ≤ t := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [hdiag]
      exact ⟨fun _ => htpos, fun _ => hjpos⟩
    · exact hsame _ (hrange x y hxy)
  constructor
  · intro hc x y z hxy hyz hxz
    have h := hc x y z hxy hyz ((heq x z).mpr hxz)
    exact ⟨(heq x y).mp h.1, (heq y z).mp h.2⟩
  · intro hc x y z hxy hyz hxz
    have h := hc x y z hxy hyz ((heq x z).mp hxz)
    exact ⟨(heq x y).mpr h.1, (heq y z).mpr h.2⟩

/-- A threshold above all distances is automatically convex. -/
theorem convexAt_of_global_bound {V : Type u} [LinearOrder V]
    (d : V → V → ℝ) {m j : ℝ}
    (hbound : ∀ x y, d x y ≤ m) (hmj : m ≤ j) :
    ConvexAt d j := by
  intro x y z _ _ _
  exact ⟨(hbound x y).trans hmj, (hbound y z).trans hmj⟩

/-- If there are no T-distances <= j, the j-relation is equality,
so convexity is automatic in any linear order. -/
theorem convexAt_of_no_distance_below {V : Type u} [LinearOrder V]
    {T : Set ℝ} (d : V → V → ℝ)
    (hdiag : ∀ x, d x x = 0)
    (hrange : ∀ x y, x ≠ y → d x y ∈ T)
    {j : ℝ} (hjpos : 0 ≤ j)
    (hnone : ∀ s ∈ T, j < s) :
    ConvexAt d j := by
  intro x y z hxy hyz hxz
  have hxz_eq : x = z := by
    by_contra hne
    exact (not_lt_of_ge hxz) (hnone _ (hrange x z hne))
  subst z
  have hxy_eq : x = y := le_antisymm hxy hyz
  subst y
  rw [hdiag]
  exact ⟨hjpos, hjpos⟩

/-- Exact convexity equivalence for every jump threshold in S and T.
All T-valued distances may be real numbers, no triangle inequality
or symmetry is needed for the purely order-theoretic transfer. -/
theorem jumpConvex_iff_of_capped_closed {S T : Set ℝ}
    {m : ℝ} {V : Type u} [LinearOrder V]
    (d : V → V → ℝ)
    (hpos : Positive S) (hT : T.Finite) (hTS : T ⊆ S)
    (hm : m ∈ T) (hbound : ∀ s ∈ T, s ≤ m)
    (hclosed : ∀ a ∈ T, ∀ b ∈ T, cappedSum S m a b ∈ T)
    (hdiag : ∀ x, d x x = 0)
    (hrange : ∀ x y, x ≠ y → d x y ∈ T) :
    JumpConvex S d ↔ JumpConvex T d := by
  have hmpos : 0 ≤ m := (hpos m (hTS hm)).le
  have hdBound : ∀ x y : V, d x y ≤ m := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [hdiag]
      exact hmpos
    · exact hbound _ (hrange x y hxy)
  constructor
  · intro hconv t hTjump
    exact hconv t (jump_of_restricted_jump hpos hTS hbound hclosed hTjump)
  · intro hconv j hSjump
    by_cases hjm : j < m
    · by_cases hne : ∃ s ∈ T, s ≤ j
      · obtain ⟨t, hTjump, hsame⟩ :=
          exists_restricted_jump_below hpos hT hTS hm hbound hclosed
            hSjump hjm hne
        have hjpos : 0 ≤ j := (hpos j hSjump.1).le
        have htpos : 0 ≤ t := (hpos t (hTS hTjump.1)).le
        exact (convexAt_iff_same_threshold d hdiag hrange
          hjpos htpos hsame).mpr (hconv t hTjump)
      · have hnone : ∀ s ∈ T, j < s := by
          intro s hs
          exact lt_of_not_ge (fun hsj => hne ⟨s, hs, hsj⟩)
        exact convexAt_of_no_distance_below d hdiag hrange
          (hpos j hSjump.1).le hnone
    · exact convexAt_of_global_bound d hdBound (le_of_not_gt hjm)

/-- The scalar finite-generation construction can choose T so that
jump-threshold convexity is preserved on any given D-valued ordered
vertex set. For nonempty D, m can be chosen as its maximum. -/
theorem exists_finite_capped_extension_convex {S D : Set ℝ}
    {m : ℝ} {V : Type u} [LinearOrder V]
    (d : V → V → ℝ)
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    (hD : D.Finite) (hDS : D ⊆ S)
    (hmD : m ∈ D) (hDm : ∀ s ∈ D, s ≤ m)
    (hdiag : ∀ x, d x x = 0)
    (hrange : ∀ x y, x ≠ y → d x y ∈ D) :
    ∃ T : Set ℝ, T.Finite ∧ D ⊆ T ∧ T ⊆ S ∧
      WellDefined T ∧ AssociativeOn T ∧
      (JumpConvex S d ↔ JumpConvex T d) := by
  obtain ⟨T, hT, hDT, hTS, hTm, hclosed, hTw, hTa⟩ :=
    exists_finite_capped_extension hpos hS hassoc (hDS hmD) hD hDS hDm
  exact ⟨T, hT, hDT, hTS, hTw, hTa,
    jumpConvex_iff_of_capped_closed d hpos hT hTS (hDT hmD)
      hTm hclosed hdiag
      (fun x y hxy => hDT (hrange x y hxy))⟩


/-- Every finite set of distances admits a finite four-values extension
which preserves exactly the jump-threshold convexity constraints on
an ordered structure using those distances. The empty set of distances
is included (then the vertex set has at most one element). -/
theorem exists_finite_fourValues_jumpConvex_extension {S D : Set ℝ}
    {V : Type u} [LinearOrder V] (d : V → V → ℝ)
    (hpos : Positive S) (hS : WellDefined S) (h4 : FourValues S)
    (hD : D.Finite) (hDS : D ⊆ S)
    (hdiag : ∀ x, d x x = 0)
    (hrange : ∀ x y, x ≠ y → d x y ∈ D) :
    ∃ T : Set ℝ, T.Finite ∧ D ⊆ T ∧ T ⊆ S ∧
      WellDefined T ∧ FourValues T ∧
      (JumpConvex S d ↔ JumpConvex T d) := by
  classical
  by_cases hne : D.Nonempty
  · let F : Finset ℝ := hD.toFinset
    have hF : F.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, hD.mem_toFinset.mpr ha⟩
    let m : ℝ := F.max' hF
    have hmD : m ∈ D := hD.mem_toFinset.mp (Finset.max'_mem F hF)
    have hDm : ∀ s ∈ D, s ≤ m := by
      intro s hs
      exact Finset.le_max' F s (hD.mem_toFinset.mpr hs)
    obtain ⟨T, hT, hDT, hTS, hTw, hTa, hconv⟩ :=
      exists_finite_capped_extension_convex d hpos hS
        (associativeOn_of_fourValues hpos hS h4)
        hD hDS hmD hDm hdiag hrange
    exact ⟨T, hT, hDT, hTS, hTw,
      fourValues_of_associativeOn (fun t ht => hpos t (hTS ht)) hTw hTa,
      hconv⟩
  · have hEmpty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hUnique : ∀ x y : V, x = y := by
      intro x y
      by_contra hxy
      have hdxy := hrange x y hxy
      simp [hEmpty] at hdxy
    have hSconv : JumpConvex S d := by
      intro j hj x y z _ _ _
      have hxy := hUnique x y
      have hyz := hUnique y z
      subst y
      subst z
      rw [hdiag]
      exact ⟨(hpos j hj.1).le, (hpos j hj.1).le⟩
    refine ⟨∅, Set.finite_empty, ?_, Set.empty_subset S, ?_, ?_, ?_⟩
    · simp [hEmpty]
    · intro a ha
      exact False.elim ha
    · intro a ha
      exact False.elim ha
    · constructor
      · intro _ j hj
        exact False.elim hj.1
      · intro _
        exact hSconv

end AllThoseRamseyClasses.Applications.MetricSaturation
