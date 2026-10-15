import AllThoseRamseyClasses.Applications.MetricFiniteBlocks

/-!
# Identification of finite jump-cut pieces with the manuscript's blocks

The 2019 paper defines a block as an inclusion-maximal subset of S
which satisfies the four-values condition and has no internal jump.
This file follows that definition literally (not the alternative
definition of a block as a connected component or a preselected
interval), proves the canonical pieces are exactly these blocks,
and derives the missing maximum-jump property of every non-top block.

The non-obvious direction is that a no-jump subset cannot straddle
an ambient jump cut. We choose its largest distance t below the cut j.
Everything else in the subset is above j and hence above 2*j >= 2*t.
Thus t would itself be an internal jump. The subset cannot straddle
j. Importantly, no claim that a one-point enlargement of an
arbitrary four-values subset preserves four-values is used.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- An inclusion-maximal four-values subset of S with no jump,
matching the paper's definition of a block. This allows empty S;
nonempty blocks are treated explicitly when choosing a representative. -/
def PaperBlock (S B : Set ℝ) : Prop :=
  B ⊆ S ∧ FourValues B ∧ NoGapJumps B ∧
    ∀ C : Set ℝ, B ⊆ C → C ⊆ S →
      FourValues C → NoGapJumps C → C ⊆ B

/-- A subset with no internal jump cannot cross an ambient proper jump.
No four-values property of the subset itself is required.
Finiteness is used only to choose the last point below the cut. -/
theorem noGap_subset_sameJumpSignature {S C : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hC : C.Finite) (hCS : C ⊆ S)
    (hno : NoGapJumps C)
    {a b : ℝ} (ha : a ∈ C) (hb : b ∈ C) :
    SameJumpSignature S a b := by
  intro j hj
  have hgap : ∀ s ∈ S, j < s → 2 * j < s :=
    ((jump_iff_gap hpos hS j).mp hj).2.2
  have hcannot : ∀ x ∈ C, ∀ y ∈ C, x ≤ j → y ≤ j := by
    intro x hx y hy hxj
    by_contra hny
    have hjy : j < y := lt_of_not_ge hny
    obtain ⟨t, ht, htj, htmax⟩ :=
      exists_max_below hC ⟨x, hx, hxj⟩
    have hty : t < y := lt_of_le_of_lt htj hjy
    apply hno t
    refine ⟨ht, ⟨y, hy, hty⟩, ?_⟩
    intro c hc htc
    by_cases hcj : c ≤ j
    · have hct : c ≤ t := htmax c hc hcj
      exact False.elim ((not_le_of_gt htc) hct)
    · have hjc : j < c := lt_of_not_ge hcj
      have hg := hgap c (hCS hc) hjc
      linarith
  exact ⟨hcannot a ha b hb, hcannot b hb a ha⟩

/-- The canonical pieces are exactly the manuscript's maximal no-jump
four-values sets, in the easy direction. -/
theorem jumpPiece_isPaperBlock {S : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S)
    (hS : WellDefined S) (h4 : FourValues S)
    {a : ℝ} (ha : a ∈ S) :
    PaperBlock S (JumpPiece S a) := by
  refine ⟨jumpPiece_subset S a,
    jumpPiece_fourValues hfin hpos hS h4 ha,
    jumpPiece_noGapJumps hfin hpos hS ha, ?_⟩
  intro C hPC hCS _h4C hnoC
  have hC : C.Finite := hfin.subset hCS
  have haC : a ∈ C := hPC (jumpPiece_self ha)
  intro b hb
  exact ⟨hCS hb, noGap_subset_sameJumpSignature hpos hS
    hC hCS hnoC haC hb⟩

/-- Every nonempty maximal no-jump four-values subset is precisely the
canonical ambient jump-cut piece containing any one of its members. -/
theorem paperBlock_eq_jumpPiece {S B : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S)
    (hS : WellDefined S) (h4 : FourValues S)
    (hblock : PaperBlock S B)
    {a : ℝ} (ha : a ∈ B) :
    B = JumpPiece S a := by
  obtain ⟨hBS, _hB4, hno, hMax⟩ := hblock
  have hBfin : B.Finite := hfin.subset hBS
  have hBP : B ⊆ JumpPiece S a := by
    intro b hb
    exact ⟨hBS hb, noGap_subset_sameJumpSignature
      hpos hS hBfin hBS hno ha hb⟩
  have hPB : JumpPiece S a ⊆ B :=
    hMax _ hBP (jumpPiece_subset S a)
      (jumpPiece_fourValues hfin hpos hS h4 (hBS ha))
      (jumpPiece_noGapJumps hfin hpos hS (hBS ha))
  exact Set.Subset.antisymm hBP hPB

/-- Two chosen distances in the same canonical piece determine exactly
the same block. -/
theorem jumpPiece_eq_of_mem {S : Set ℝ} {a b : ℝ}
    (hb : b ∈ JumpPiece S a) :
    JumpPiece S a = JumpPiece S b := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, sameJumpSignature_trans
      (sameJumpSignature_symm hb.2) hx.2⟩
  · intro hx
    exact ⟨hx.1, sameJumpSignature_trans hb.2 hx.2⟩

/-- Every non-top block of a finite four-values distance set
has a maximum which is a proper *ambient* jump, the representation
fact required by the corrected zero-radius Lemma samedist. -/
theorem paperBlock_proper_max_isJump {S B : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S)
    (hS : WellDefined S) (h4 : FourValues S)
    (hblock : PaperBlock S B)
    (hne : B.Nonempty)
    {m : ℝ} (hm : m ∈ B)
    (hmax : ∀ x ∈ B, x ≤ m)
    (hproper : ∃ b ∈ S, m < b) :
    Jump S m := by
  obtain ⟨a, ha⟩ := hne
  have haS : a ∈ S := hblock.1 ha
  have heq : B = JumpPiece S a :=
    paperBlock_eq_jumpPiece hfin hpos hS h4 hblock ha
  have hmP : m ∈ JumpPiece S a := by
    rw [← heq]
    exact hm
  have hmaxP : ∀ x ∈ JumpPiece S a, x ≤ m := by
    intro x hx
    apply hmax x
    rw [heq]
    exact hx
  exact jumpPiece_max_isJump hpos hS hmP hmaxP hproper

end AllThoseRamseyClasses.Applications.MetricSaturation
