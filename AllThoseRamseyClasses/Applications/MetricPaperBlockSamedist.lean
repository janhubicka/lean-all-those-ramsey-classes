import AllThoseRamseyClasses.Applications.MetricFiniteBlockMaximal
import AllThoseRamseyClasses.Applications.MetricJumpSamedist
import AllThoseRamseyClasses.Applications.MetricFiniteWellDefined

/-!
# The published finite-block interface to Lemma samedist

For a finite positive four-values distance set S, the paper's
inclusion-maximal no-jump four-values blocks are now defined and
verified in MetricFiniteBlockMaximal.

Here we eliminate the previously assumed maximum-of-block premise.
Indeed, ANY no-jump subset B containing an ambient jump j has
j=max(B): otherwise B would cross the jump cut at j and its last
member below j would be an internal jump of B.

The original lemma permits zero as a jump parameter; that case
uses the trivial block {0}, not a subset of positive S.
The two cases are combined in PaperBlockAtLevel.

No new metric lift, shortcut completion, or Ramsey theorem is
claimed by this module.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Every maximal no-jump block containing a specified positive
ambient jump j ends at j. In fact four-values and maximality of B
are not used in the short no-straddling argument. -/
theorem paperBlock_containing_jump_max {S B : Set ℝ} {j : ℝ}
    (hfin : S.Finite) (hpos : Positive S) (hS : WellDefined S)
    (hblock : PaperBlock S B)
    (hj : Jump S j) (hjB : j ∈ B) :
    ∀ b ∈ B, b ≤ j := by
  intro b hb
  have hsign := noGap_subset_sameJumpSignature hpos hS
    (hfin.subset hblock.1) hblock.1 hblock.2.2.1 hjB hb
  exact (hsign j hj).mp (le_refl j)

/-- The paper's positive blocks at a jump, together with its
explicitly adjoined singleton zero-equivalence. -/
def PaperBlockAtLevel (S B : Set ℝ) (j : ℝ) : Prop :=
  (j = 0 ∧ B = {0}) ∨
    (Jump S j ∧ PaperBlock S B ∧ j ∈ B)

/-- Both kinds of manuscript blocks have exactly the bounded
threshold needed by the zero-adjoined sandwich theorem. -/
theorem paperBlockAtLevel_bounds {S B : Set ℝ} {j : ℝ}
    (hfin : S.Finite) (hpos : Positive S) (hS : WellDefined S)
    (hB : PaperBlockAtLevel S B j) :
    j ∈ B ∧ (∀ b ∈ B, b ≤ j) ∧ (j = 0 ∨ Jump S j) := by
  rcases hB with ⟨hj, hBzero⟩ | ⟨hj, hblock, hjB⟩
  · subst j
    subst B
    refine ⟨by simp, ?_, Or.inl rfl⟩
    intro b hb
    have hzero : b = 0 := by simpa using hb
    subst b
    exact le_refl _
  · exact ⟨hjB, paperBlock_containing_jump_max hfin hpos hS
      hblock hj hjB, Or.inr hj⟩

/-- Every proper jump belongs to its canonical paper block,
and the zero level belongs to its trivial block. -/
theorem exists_paperBlockAtLevel {S : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S)
    (hS : WellDefined S) (h4 : FourValues S)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) :
    ∃ B : Set ℝ, PaperBlockAtLevel S B j := by
  rcases hj with hzero | hj
  · refine ⟨{0}, Or.inl ⟨hzero, rfl⟩⟩
  · exact ⟨JumpPiece S j,
      Or.inr ⟨hj, jumpPiece_isPaperBlock hfin hpos hS h4 hj.1,
        jumpPiece_self hj.1⟩⟩

/-- Two paper blocks containing the same positive ambient jump
coincide. This is a finite-block uniqueness statement, not an
assumption about how a block is selected. -/
theorem paperBlock_unique_at_jump {S B₁ B₂ : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S)
    (hS : WellDefined S) (h4 : FourValues S)
    {j : ℝ} (hj : Jump S j)
    (hB₁ : PaperBlock S B₁) (hB₂ : PaperBlock S B₂)
    (hj₁ : j ∈ B₁) (hj₂ : j ∈ B₂) :
    B₁ = B₂ := by
  calc
    B₁ = JumpPiece S j :=
      paperBlock_eq_jumpPiece hfin hpos hS h4 hB₁ hj₁
    _ = B₂ :=
      (paperBlock_eq_jumpPiece hfin hpos hS h4 hB₂ hj₂).symm

/-- Corrected finite-S version of the paper's Lemma samedist.
The block maxima are no longer hypotheses: they follow from
the literal maximal-no-jump block definition. The roots are
different, as they are for disjoint equivalence classes.
All zero-radius cases are covered, and ell belongs to S. -/
theorem finite_paperBlock_samedist {S B₁ B₂ : Set ℝ} {V : Type u}
    (hfin : S.Finite) (hpos : Positive S) (hS : WellDefined S)
    (h4 : FourValues S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j₁ j₂ : ℝ)
    (hB₁ : PaperBlockAtLevel S B₁ j₁)
    (hB₂ : PaperBlockAtLevel S B₂ j₂)
    (root₁ root₂ : V) (hroots : root₁ ≠ root₂) :
    ∃ ell : ℝ, ell ∈ S ∧
      ∀ u : V, (∃ b ∈ B₁, d u root₁ ≤ b) →
        ∀ v : V, (∃ b ∈ B₂, d v root₂ ≤ b) →
          sumWithZero S (sumWithZero S j₁ (d u v)) j₂ = ell := by
  obtain ⟨hj₁B, hmax₁, hj₁⟩ :=
    paperBlockAtLevel_bounds hfin hpos hS hB₁
  obtain ⟨hj₂B, hmax₂, hj₂⟩ :=
    paperBlockAtLevel_bounds hfin hpos hS hB₂
  exact metric_samedist_bounded_blocks_distinct hpos hS
    (associativeOn_of_fourValues hpos hS h4) hd
    B₁ B₂ j₁ j₂ hj₁ hj₂ hj₁B hmax₁ hj₂B hmax₂
    root₁ root₂ hroots

/-- Disjoint jump-equivalence classes are represented by distinct
roots. Hence the finite-S paper lemma follows with the manuscript's
disjointness premise rather than a separate distinct-root premise. -/
theorem finite_paperBlock_samedist_disjoint {S B₁ B₂ : Set ℝ}
    {V : Type u}
    (hfin : S.Finite) (hpos : Positive S) (hS : WellDefined S)
    (h4 : FourValues S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j₁ j₂ : ℝ)
    (hB₁ : PaperBlockAtLevel S B₁ j₁)
    (hB₂ : PaperBlockAtLevel S B₂ j₂)
    (root₁ root₂ : V)
    (hdisjoint :
      Disjoint
        {u : V | ∃ b ∈ B₁, d u root₁ ≤ b}
        {v : V | ∃ b ∈ B₂, d v root₂ ≤ b}) :
    ∃ ell : ℝ, ell ∈ S ∧
      ∀ u : V, (∃ b ∈ B₁, d u root₁ ≤ b) →
        ∀ v : V, (∃ b ∈ B₂, d v root₂ ≤ b) →
          sumWithZero S (sumWithZero S j₁ (d u v)) j₂ = ell := by
  obtain ⟨hj₁B, _, hj₁⟩ :=
    paperBlockAtLevel_bounds hfin hpos hS hB₁
  obtain ⟨hj₂B, _, hj₂⟩ :=
    paperBlockAtLevel_bounds hfin hpos hS hB₂
  have hroots : root₁ ≠ root₂ := by
    intro heq
    have hroot₁ : ∃ b ∈ B₁, d root₁ root₁ ≤ b := by
      refine ⟨j₁, hj₁B, ?_⟩
      rw [hd.diag root₁]
      exact threshold_nonneg hpos hj₁
    have hroot₂ : ∃ b ∈ B₂, d root₁ root₂ ≤ b := by
      rw [heq]
      refine ⟨j₂, hj₂B, ?_⟩
      rw [hd.diag root₂]
      exact threshold_nonneg hpos hj₂
    exact (Set.disjoint_left.mp hdisjoint) hroot₁ hroot₂
  exact finite_paperBlock_samedist hfin hpos hS h4 hd
    j₁ j₂ hB₁ hB₂ root₁ root₂ hroots


/-- The literal manuscript level language: its jump predicate is
the elementary gap condition, and the zero level uses {0}.
No rounded-sum well-definedness assumption is embedded in this
definition. -/
def PaperGapBlockAtLevel (S B : Set ℝ) (j : ℝ) : Prop :=
  (j = 0 ∧ B = {0}) ∨
    (GapJump S j ∧ PaperBlock S B ∧ j ∈ B)

/-- On finite positive distance sets, the paper's gap-jump level
supplies exactly the idempotent jump required by the corrected
sandwich lemma; well-definedness is automatic and not an extra
paper hypothesis. -/
theorem paperGapBlockAtLevel_to_jump {S B : Set ℝ} {j : ℝ}
    (hfin : S.Finite) (hpos : Positive S)
    (hB : PaperGapBlockAtLevel S B j) :
    PaperBlockAtLevel S B j := by
  rcases hB with hzero | ⟨hgap, hblock, hjB⟩
  · exact Or.inl hzero
  · have hS : WellDefined S := wellDefined_of_finite hfin hpos
    exact Or.inr ⟨(gapJump_iff_Jump hpos hS j).mp hgap, hblock, hjB⟩

/-- The manuscript's stated hypotheses on a finite four-values S
suffice for the corrected Lemma samedist. No independent condition
on rounded-sum attainment or on block maxima is supplied. Blocks
are literal inclusion-maximal no-jump four-values subsets, jumps
are their original gap-defined levels, and zero is the trivial
singleton block. This includes the disjointness hypothesis of the
published lemma and yields a genuine S-valued constant. -/
theorem finite_paperBlock_samedist_published {S B₁ B₂ : Set ℝ}
    {V : Type u}
    (hfin : S.Finite) (hpos : Positive S)
    (h4 : FourValues S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j₁ j₂ : ℝ)
    (hB₁ : PaperGapBlockAtLevel S B₁ j₁)
    (hB₂ : PaperGapBlockAtLevel S B₂ j₂)
    (root₁ root₂ : V)
    (hdisjoint :
      Disjoint
        {u : V | ∃ b ∈ B₁, d u root₁ ≤ b}
        {v : V | ∃ b ∈ B₂, d v root₂ ≤ b}) :
    ∃ ell : ℝ, ell ∈ S ∧
      ∀ u : V, (∃ b ∈ B₁, d u root₁ ≤ b) →
        ∀ v : V, (∃ b ∈ B₂, d v root₂ ≤ b) →
          sumWithZero S (sumWithZero S j₁ (d u v)) j₂ = ell := by
  have hS : WellDefined S := wellDefined_of_finite hfin hpos
  exact finite_paperBlock_samedist_disjoint hfin hpos hS h4 hd
    j₁ j₂
    (paperGapBlockAtLevel_to_jump hfin hpos hB₁)
    (paperGapBlockAtLevel_to_jump hfin hpos hB₂)
    root₁ root₂ hdisjoint

/-- Each gap-defined positive jump belongs to a unique maximal
four-values no-jump block; the zero level uses the trivial class.
This reconstructs the finite-S block assignment rather than
assuming existence of a selected block. -/
theorem exists_paperGapBlockAtLevel {S : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S) (h4 : FourValues S)
    (j : ℝ) (hj : j = 0 ∨ GapJump S j) :
    ∃ B : Set ℝ, PaperGapBlockAtLevel S B j := by
  rcases hj with hzero | hj
  · exact ⟨{0}, Or.inl ⟨hzero, rfl⟩⟩
  · have hS : WellDefined S := wellDefined_of_finite hfin hpos
    have hjJ : Jump S j := (gapJump_iff_Jump hpos hS j).mp hj
    exact ⟨JumpPiece S j, Or.inr
      ⟨hj, jumpPiece_isPaperBlock hfin hpos hS h4 hjJ.1,
        jumpPiece_self hjJ.1⟩⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
