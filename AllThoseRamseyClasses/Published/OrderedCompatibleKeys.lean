import AllThoseRamseyClasses.Published.OrderedRankStrictness
import Mathlib.Order.Prod.Lex.Basic

/-!
# Compatible lexicographic keys for a strong ordered amalgam

The order on a strong free-amalgam carrier can be recovered from
compatible side keys. The first coordinate is the number of root
vertices below x. Moving vertices are placed before the next
root vertex at the same cut. Left-only and right-only vertices
get different private priorities 0 and 1, while the common root
has priority 2.

The third coordinate records the strict rank within each side
(or the root cut rank for a shared vertex). The keys agree at
every embedded root vertex, and are STRICTLY increasing along
the old side orders. This is the essential order-extension step;
building the resulting global order remains a separate lemma.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- A root vertex gets common priority 2 and its shared root
rank. Side-only vertices get their private priority and the
order rank of the containing side. -/
noncomputable def sideOrderKey
    {D X : Type} [Fintype D] [Fintype X]
    {Root : RelStructure Lang D}
    (Side : RelStructure Lang X) (s : Embedding Root Side)
    (privatePriority : ℕ) (x : X) : ℕ ×ₗ (ℕ ×ₗ ℕ) := by
  classical
  exact if hx : ∃ d : D, s d = x then
    toLex (rootCut Side s x, toLex (2, rootCut Side s x))
  else
    toLex (rootCut Side s x,
      toLex (privatePriority, sideOrderRank Side x))

/-- The two side key maps agree on every identified root vertex,
even though their private priorities differ. -/
theorem sideOrderKey_root_agree
    {D E F : Type} [Fintype D] [Fintype E] [Fintype F]
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E} {Right : RelStructure Lang F}
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (d : D) :
    sideOrderKey Left sL 0 (sL d) =
      sideOrderKey Right sR 1 (sR d) := by
  classical
  have hL : ∃ x : D, sL x = sL d := ⟨d, rfl⟩
  have hR : ∃ x : D, sR x = sR d := ⟨d, rfl⟩
  have hEq : rootCut Left sL (sL d) =
      rootCut Right sR (sR d) :=
    rootCut_agree_on_root sL sR d
  simp only [sideOrderKey, dif_pos hL, dif_pos hR]
  rw [hEq]

/-- Every private priority strictly below 2 preserves the order
on its side. Cases with an earlier root and equal cuts are
ruled out by the strict root-cut lemma. -/
theorem sideOrderKey_strictMono
    {D X : Type} [Fintype D] [Fintype X]
    {Root : RelStructure Lang D}
    (Side : RelStructure Lang X) (hSide : pairedClass Side)
    (s : Embedding Root Side) (privatePriority : ℕ)
    (hPriority : privatePriority < 2)
    {x y : X} (hxy : edge Side .lt x y) :
    sideOrderKey Side s privatePriority x <
      sideOrderKey Side s privatePriority y := by
  classical
  have hCutLe : rootCut Side s x ≤ rootCut Side s y :=
    rootCut_mono hSide s hxy
  by_cases hCutLt : rootCut Side s x < rootCut Side s y
  · unfold sideOrderKey
    split_ifs <;>
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hCutLt)
  · have hEq : rootCut Side s x = rootCut Side s y := by
      omega
    by_cases hRootX : ∃ d : D, s d = x
    · obtain ⟨d, hd⟩ := hRootX
      have hStrict : rootCut Side s (s d) < rootCut Side s y :=
        rootCut_strict_after_root hSide s d y (by simpa [hd] using hxy)
      rw [hd] at hStrict
      omega
    · by_cases hRootY : ∃ d : D, s d = y
      · have hLex : toLex
            (rootCut Side s x,
              toLex (privatePriority, sideOrderRank Side x)) <
            toLex
            (rootCut Side s y, toLex (2, rootCut Side s y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inl hPriority)⟩)
        simpa only [sideOrderKey, dif_neg hRootX,
          dif_pos hRootY] using hLex
      · have hRank : sideOrderRank Side x < sideOrderRank Side y :=
          sideOrderRank_strictMono Side hSide hxy
        have hLex : toLex
            (rootCut Side s x,
              toLex (privatePriority, sideOrderRank Side x)) <
            toLex
              (rootCut Side s y,
                toLex (privatePriority, sideOrderRank Side y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hRank⟩)⟩)
        simpa only [sideOrderKey, dif_neg hRootX,
          dif_neg hRootY] using hLex

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
