import AllThoseRamseyClasses.Applications.MetricPaperBlockSamedist
import AllThoseRamseyClasses.Applications.MetricConvexityTransfer

/-!
# Finite metric block-convex orders are jump-convex orders

The published Ramsey lift uses orders convex for every block
equivalence, while the finite-distance reduction was formulated
using jump-threshold convexity. For finite positive four-values S,
these are exactly the same requirement, on actual S-metrics.

Every manuscript block B is an inclusion-maximal no-jump
four-values subset. The relation for B is the paper's literal
exists-b-in-B distance threshold, not a guessed equivalent
relation. For a non-top block, its largest member is an ambient
jump, so its convexity follows from jump convexity. For a top
block, the relation is universal and its convexity is automatic.

Conversely, every proper jump j belongs to a unique canonical
block B_j and is its maximum. Convexity for that block gives
convexity of the j-threshold. This file makes no statement
about general infinite S or the still-unfinished metric lift.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Literal convexity for the paper's block-equivalence relations:
if the endpoints of an ordered triple are within one block threshold,
then the intermediate vertex lies in that class too. -/
def PaperBlockConvex {V : Type u} [LinearOrder V]
    (S : Set ℝ) (d : V → V → ℝ) : Prop :=
  ∀ B : Set ℝ, PaperBlock S B →
    ∀ x y z : V, x ≤ y → y ≤ z →
      (∃ b ∈ B, d x z ≤ b) →
        (∃ b ∈ B, d x y ≤ b) ∧
        (∃ b ∈ B, d y z ≤ b)

/-- A nonempty block of finite S has a largest member.
No jump or four-values assumption is needed for this finiteness
argument beyond being a subset of S. -/
theorem paperBlock_exists_max {S B : Set ℝ}
    (hfin : S.Finite) (hB : PaperBlock S B)
    (hne : B.Nonempty) :
    ∃ m ∈ B, ∀ b ∈ B, b ≤ m := by
  have hBfin : B.Finite := hfin.subset hB.1
  let F : Finset ℝ := hBfin.toFinset
  obtain ⟨b, hb⟩ := hne
  have hF : F.Nonempty := ⟨b, hBfin.mem_toFinset.mpr hb⟩
  let m : ℝ := F.max' hF
  refine ⟨m, hBfin.mem_toFinset.mp (Finset.max'_mem F hF), ?_⟩
  intro x hx
  exact Finset.le_max' F x (hBfin.mem_toFinset.mpr hx)

/-- Every jump-convex metric order is convex for all of the
paper's finite-S block equivalences, including the top block
whose relation is universal. -/
theorem paperBlockConvex_of_jumpConvex {S : Set ℝ}
    {V : Type u} [LinearOrder V]
    (hfin : S.Finite) (hpos : Positive S)
    (h4 : FourValues S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (hconv : JumpConvex S d) :
    PaperBlockConvex S d := by
  have hS : WellDefined S := wellDefined_of_finite hfin hpos
  intro B hB x y z hxy hyz
  rintro ⟨b, hb, hxb⟩
  obtain ⟨m, hm, hmax⟩ := paperBlock_exists_max hfin hB ⟨b, hb⟩
  by_cases hproper : ∃ s ∈ S, m < s
  · have hj : Jump S m :=
      paperBlock_proper_max_isJump hfin hpos hS h4 hB
        ⟨b, hb⟩ hm hmax hproper
    have hmXZ : d x z ≤ m := hxb.trans (hmax b hb)
    obtain ⟨hmXY, hmYZ⟩ := hconv m hj x y z hxy hyz hmXZ
    exact ⟨⟨m, hm, hmXY⟩, ⟨m, hm, hmYZ⟩⟩
  · have hmaxS : ∀ s ∈ S, s ≤ m := by
      intro s hs
      by_contra hns
      exact hproper ⟨s, hs, lt_of_not_ge hns⟩
    have hdist : ∀ s t : V, d s t ≤ m := by
      intro s t
      by_cases hst : s = t
      · subst t
        rw [hd.diag s]
        exact (hpos m (hB.1 hm)).le
      · exact hmaxS _ (hd.values s t hst)
    exact ⟨⟨m, hm, hdist x y⟩, ⟨m, hm, hdist y z⟩⟩

/-- Convexity for all original paper blocks implies convexity
at every proper jump threshold, using the canonical block at j. -/
theorem jumpConvex_of_paperBlockConvex {S : Set ℝ}
    {V : Type u} [LinearOrder V]
    (hfin : S.Finite) (hpos : Positive S)
    (h4 : FourValues S)
    {d : V → V → ℝ}
    (hconv : PaperBlockConvex S d) :
    JumpConvex S d := by
  have hS : WellDefined S := wellDefined_of_finite hfin hpos
  intro j hj x y z hxy hyz hxz
  let B := JumpPiece S j
  have hB : PaperBlock S B :=
    jumpPiece_isPaperBlock hfin hpos hS h4 hj.1
  have hjB : j ∈ B := jumpPiece_self hj.1
  have hmax : ∀ b ∈ B, b ≤ j :=
    paperBlock_containing_jump_max hfin hpos hS hB hj hjB
  obtain ⟨⟨b, hb, hxyB⟩, ⟨c, hc, hyzB⟩⟩ :=
    hconv B hB x y z hxy hyz ⟨j, hjB, hxz⟩
  exact ⟨hxyB.trans (hmax b hb), hyzB.trans (hmax c hc)⟩

/-- For finite positive four-values distance sets, the manuscript's
block-convexity is *exactly* convexity at proper ambient jump
thresholds, for a genuine S-metric distance map. -/
theorem paperBlockConvex_iff_jumpConvex {S : Set ℝ}
    {V : Type u} [LinearOrder V]
    (hfin : S.Finite) (hpos : Positive S)
    (h4 : FourValues S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    PaperBlockConvex S d ↔ JumpConvex S d := by
  constructor
  · exact jumpConvex_of_paperBlockConvex hfin hpos h4
  · exact paperBlockConvex_of_jumpConvex hfin hpos h4 hd

end AllThoseRamseyClasses.Applications.MetricSaturation
