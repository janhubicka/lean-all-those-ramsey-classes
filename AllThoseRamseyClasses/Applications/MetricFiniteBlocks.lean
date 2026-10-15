import AllThoseRamseyClasses.Applications.MetricJumpThresholds

/-!
# Canonical finite blocks from ambient jump cuts

For a finite positive four-values distance set S, divide S according
to the signatures of its proper ambient jump thresholds:
a and b belong to the same piece iff (a <= j ↔ b <= j) for
every proper jump j of S.

The main elementary observations are:

* each piece is closed under the ambient rounded sum capped at its
  maximum, hence has its own well-defined four-values operation;
* a proper jump within one piece would also be an ambient jump,
  contradicting the common jump-cut signature;
* the maximum of a non-top piece is itself an ambient jump.

These statements do NOT assume that S has finitely many blocks,
nor that adding one distance to a four-values subset preserves
four-values. The maximality comparison with the manuscript's
definition of a block is in MetricFiniteBlockMaximal.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The paper's gap definition of a jump, without any requirement
that rounded sums already be well-defined on the tested subset. -/
def GapJump (S : Set ℝ) (j : ℝ) : Prop :=
  j ∈ S ∧ (∃ b ∈ S, j < b) ∧
    ∀ b ∈ S, j < b → 2 * j < b

/-- No internal jump in the literal sense of the manuscript. -/
def NoGapJumps (S : Set ℝ) : Prop :=
  ∀ j, ¬ GapJump S j

theorem gapJump_iff_Jump {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (j : ℝ) :
    GapJump S j ↔ Jump S j :=
  (jump_iff_gap hpos hS j).symm

/-- Equal signatures across every ambient proper jump cut. -/
def SameJumpSignature (S : Set ℝ) (a b : ℝ) : Prop :=
  ∀ j, Jump S j → (a ≤ j ↔ b ≤ j)

theorem sameJumpSignature_refl (S : Set ℝ) (a : ℝ) :
    SameJumpSignature S a a := by
  intro j hj
  rfl

theorem sameJumpSignature_symm {S : Set ℝ} {a b : ℝ}
    (hab : SameJumpSignature S a b) :
    SameJumpSignature S b a := by
  intro j hj
  exact (hab j hj).symm

theorem sameJumpSignature_trans {S : Set ℝ} {a b c : ℝ}
    (hab : SameJumpSignature S a b)
    (hbc : SameJumpSignature S b c) :
    SameJumpSignature S a c := by
  intro j hj
  exact (hab j hj).trans (hbc j hj)

/-- The full canonical piece of a chosen allowed distance. -/
def JumpPiece (S : Set ℝ) (a : ℝ) : Set ℝ :=
  {b | b ∈ S ∧ SameJumpSignature S a b}

theorem jumpPiece_self {S : Set ℝ} {a : ℝ} (ha : a ∈ S) :
    a ∈ JumpPiece S a :=
  ⟨ha, sameJumpSignature_refl S a⟩

theorem jumpPiece_subset (S : Set ℝ) (a : ℝ) :
    JumpPiece S a ⊆ S :=
  fun _ h => h.1

theorem jumpPiece_finite {S : Set ℝ} (hfin : S.Finite) (a : ℝ) :
    (JumpPiece S a).Finite :=
  hfin.subset (jumpPiece_subset S a)

/-- A canonical piece of a finite S has a greatest member. -/
theorem exists_jumpPiece_max {S : Set ℝ} (hfin : S.Finite)
    {a : ℝ} (ha : a ∈ S) :
    ∃ m ∈ JumpPiece S a, ∀ x ∈ JumpPiece S a, x ≤ m := by
  let P := JumpPiece S a
  have hP : P.Finite := jumpPiece_finite hfin a
  let F : Finset ℝ := hP.toFinset
  have hF : F.Nonempty := by
    exact ⟨a, hP.mem_toFinset.mpr (jumpPiece_self ha)⟩
  let m : ℝ := F.max' hF
  refine ⟨m, hP.mem_toFinset.mp (Finset.max'_mem F hF), ?_⟩
  intro x hx
  exact Finset.le_max' F x (hP.mem_toFinset.mpr hx)

/-- Capping at the largest member of one jump-signature piece
never leaves that piece. The proof uses exactly the ambient cut
signatures and the fact that a positive rounded sum dominates its
operands up to the cap. -/
theorem jumpPiece_capped_closed {S : Set ℝ} {a m : ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hm : m ∈ JumpPiece S a)
    (hmax : ∀ x ∈ JumpPiece S a, x ≤ m) :
    ∀ x ∈ JumpPiece S a, ∀ y ∈ JumpPiece S a,
      cappedSum S m x y ∈ JumpPiece S a := by
  intro x hx y hy
  have hmem : cappedSum S m x y ∈ S :=
    cappedSum_mem hS hm.1 hx.1 hy.1
  refine ⟨hmem, ?_⟩
  intro j hj
  have hsameM := hm.2 j hj
  have hsameX := hx.2 j hj
  by_cases hmj : m ≤ j
  · have haj : a ≤ j := hsameM.mpr hmj
    have hresult : cappedSum S m x y ≤ j :=
      (min_le_left _ _).trans hmj
    exact ⟨fun _ => hresult, fun _ => haj⟩
  · have hnaj : ¬ a ≤ j := fun haj => hmj (hsameM.mp haj)
    have hnxj : ¬ x ≤ j := fun hxj => hnaj (hsameX.mpr hxj)
    have hxle : x ≤ cappedSum S m x y :=
      le_cappedSum hx.1 (hmax x hx) (by linarith [hpos y hy.1])
    have hnresult : ¬ cappedSum S m x y ≤ j :=
      fun hresult => hnxj (hxle.trans hresult)
    exact ⟨fun haj => False.elim (hnaj haj),
      fun hresult => False.elim (hnresult hresult)⟩

/-- The canonical pieces are genuine four-values distance sets,
even though arbitrary subsets of S need not inherit four-values. -/
theorem jumpPiece_fourValues {S : Set ℝ} (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    (h4 : FourValues S) {a : ℝ} (ha : a ∈ S) :
    FourValues (JumpPiece S a) := by
  obtain ⟨m, hm, hmax⟩ := exists_jumpPiece_max hfin ha
  have hclosed := jumpPiece_capped_closed hpos hS hm hmax
  have hp : Positive (JumpPiece S a) :=
    fun x hx => hpos x hx.1
  have hw : WellDefined (JumpPiece S a) :=
    wellDefined_subset hpos (jumpPiece_subset S a) hmax hclosed
  have hAssoc : AssociativeOn (JumpPiece S a) :=
    associativeOn_subset hpos hS
      (associativeOn_of_fourValues hpos hS h4)
      hm.1 (jumpPiece_subset S a) hmax hclosed
  exact fourValues_of_associativeOn hp hw hAssoc

/-- No canonical piece has a proper jump in the manuscript's sense.
Every putative internal jump would also be an ambient jump separating
two members of the very same signature class. -/
theorem jumpPiece_noGapJumps {S : Set ℝ} (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {a : ℝ} (ha : a ∈ S) :
    NoGapJumps (JumpPiece S a) := by
  obtain ⟨m, hm, hmax⟩ := exists_jumpPiece_max hfin ha
  have hclosed := jumpPiece_capped_closed hpos hS hm hmax
  have hp : Positive (JumpPiece S a) :=
    fun x hx => hpos x hx.1
  have hw : WellDefined (JumpPiece S a) :=
    wellDefined_subset hpos (jumpPiece_subset S a) hmax hclosed
  intro t htGap
  have htJump : Jump (JumpPiece S a) t :=
    (gapJump_iff_Jump hp hw t).mp htGap
  have hj : Jump S t :=
    jump_of_restricted_jump hpos (jumpPiece_subset S a) hmax
      hclosed htJump
  obtain ⟨u, hu, htu⟩ := htJump.2.1
  have hsameT := (htJump.1).2 t hj
  have hsameU := hu.2 t hj
  have htu_le : u ≤ t :=
    (hsameU.mp (hsameT.mpr (le_refl t)))
  exact (not_le_of_gt htu) htu_le

/-- A non-top canonical piece ends exactly at an ambient proper jump,
without any assumption that every intermediate finite subset has the
four-values property. -/
theorem jumpPiece_max_isJump {S : Set ℝ} {a m : ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hm : m ∈ JumpPiece S a)
    (hmax : ∀ x ∈ JumpPiece S a, x ≤ m)
    (hproper : ∃ b ∈ S, m < b) :
    Jump S m := by
  by_contra hnot
  have hnotgap : ¬ (∀ b ∈ S, m < b → 2 * m < b) := by
    intro hgap
    exact hnot ((jump_iff_gap hpos hS m).mpr
      ⟨hm.1, hproper, hgap⟩)
  push_neg at hnotgap
  obtain ⟨s, hs, hms, hsle⟩ := hnotgap
  have hsignature : SameJumpSignature S m s := by
    intro j hj
    constructor
    · intro hmj
      by_contra hnsj
      have hjs : j < s := lt_of_not_ge hnsj
      have hjgap := ((jump_iff_gap hpos hS j).mp hj).2.2 s hs hjs
      linarith
    · intro hsj
      exact (le_of_lt hms).trans hsj
  have hsp : s ∈ JumpPiece S a :=
    ⟨hs, sameJumpSignature_trans hm.2 hsignature⟩
  exact (not_le_of_gt hms) (hmax s hsp)

end AllThoseRamseyClasses.Applications.MetricSaturation
