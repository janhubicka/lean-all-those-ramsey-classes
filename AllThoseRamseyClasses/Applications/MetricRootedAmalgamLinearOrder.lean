import AllThoseRamseyClasses.Applications.MetricRootedAmalgamOverlap
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# A common linear order on an identified-base metric amalgam

This is the order-extension component for two arbitrary FINITE
linearly ordered vertex sets U and V, over compatible embeddings
of the SAME common finite root A. We do not assume any metric
or convexity property at this stage.

The key of a vertex starts with the number of root vertices
preceding it. In each cut, private U-vertices precede private
V-vertices and both precede the next root vertex. A last
coordinate keeps the original within-side order. The root
key does not depend on which side supplies its representative.

The resulting genuine linear order on the identified-root
carrier preserves BOTH old linear orders. It does not, by
itself, imply convexity at S-metric jumps; that is the next
separate geometric obligation, not a consequence of plain
finite order amalgamation.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Number of common root vertices preceding a side vertex. -/
private noncomputable def metricRootCut
    {A : Type u} {X : Type v}
    [Fintype A] [LinearOrder X]
    (i : A → X) (x : X) : ℕ :=
  ((Finset.univ : Finset A).filter (fun a => i a < x)).card

/-- Strict rank of a vertex in its original finite side order. -/
private noncomputable def metricSideRank
    {X : Type v} [Fintype X] [LinearOrder X] (x : X) : ℕ :=
  ((Finset.univ : Finset X).filter (fun y => y < x)).card

private theorem metricRootCut_mono
    {A : Type u} {X : Type v}
    [Fintype A] [LinearOrder X]
    (i : A → X) {x y : X} (hxy : x < y) :
    metricRootCut i x ≤ metricRootCut i y := by
  unfold metricRootCut
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact lt_trans ha hxy

private theorem metricRootCut_strict_after_root
    {A : Type u} {X : Type v}
    [Fintype A] [LinearOrder X]
    (i : A → X) (a : A) (x : X) (h : i a < x) :
    metricRootCut i (i a) < metricRootCut i x := by
  unfold metricRootCut
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨a, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl (i a)
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb ⊢
    rcases hb with rfl | hba
    · exact h
    · exact lt_trans hba h

private theorem metricSideRank_strict
    {X : Type v} [Fintype X] [LinearOrder X]
    {x y : X} (hxy : x < y) :
    metricSideRank x < metricSideRank y := by
  unfold metricSideRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl x
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hzx
    · exact hxy
    · exact lt_trans hzx hxy

/-- The root cut agrees on the two sides exactly when the
embedded root orders agree. -/
private theorem metricRootCut_root_agree
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hCompat : ∀ a b : A, iU a < iU b ↔ iV a < iV b)
    (a : A) :
    metricRootCut iU (iU a) = metricRootCut iV (iV a) := by
  unfold metricRootCut
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hCompat b a

/-- Compatible root-cut keys, with common root priority 2. -/
private noncomputable def metricSideKey
    {A : Type u} {X : Type v}
    [Fintype A] [Fintype X] [LinearOrder X]
    (i : A → X) (priority : ℕ) (x : X) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) := by
  classical
  exact if hx : ∃ a : A, i a = x then
    toLex (metricRootCut i x, toLex (2, metricRootCut i x))
  else
    toLex (metricRootCut i x, toLex (priority, metricSideRank x))

private theorem metricSideKey_root_agree
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [Fintype U] [Fintype V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hCompat : ∀ a b : A, iU a < iU b ↔ iV a < iV b)
    (a : A) :
    metricSideKey iU 0 (iU a) = metricSideKey iV 1 (iV a) := by
  classical
  have hU : ∃ b : A, iU b = iU a := ⟨a, rfl⟩
  have hV : ∃ b : A, iV b = iV a := ⟨a, rfl⟩
  simp only [metricSideKey, dif_pos hU, dif_pos hV]
  rw [metricRootCut_root_agree iU iV hCompat a]

/-- Every private side key increases strictly in that side's
linear order. No convexity, no metric assumptions. -/
private theorem metricSideKey_strict
    {A : Type u} {X : Type v}
    [Fintype A] [Fintype X] [LinearOrder X]
    (i : A → X) (priority : ℕ) (hp : priority < 2)
    {x y : X} (hxy : x < y) :
    metricSideKey i priority x < metricSideKey i priority y := by
  classical
  have hCut : metricRootCut i x ≤ metricRootCut i y :=
    metricRootCut_mono i hxy
  by_cases hStrict : metricRootCut i x < metricRootCut i y
  · unfold metricSideKey
    split_ifs <;>
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hStrict)
  · have hEq : metricRootCut i x = metricRootCut i y := by omega
    by_cases hRootX : ∃ a : A, i a = x
    · obtain ⟨a, ha⟩ := hRootX
      have hWrong := metricRootCut_strict_after_root i a y
        (by simpa [ha] using hxy)
      rw [ha] at hWrong
      omega
    · by_cases hRootY : ∃ a : A, i a = y
      · have hLex : toLex
            (metricRootCut i x,
              toLex (priority, metricSideRank x)) <
          toLex
            (metricRootCut i y,
              toLex (2, metricRootCut i y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inl hp)⟩)
        simpa only [metricSideKey, dif_neg hRootX,
          dif_pos hRootY] using hLex
      · have hRank : metricSideRank x < metricSideRank y :=
          metricSideRank_strict hxy
        have hLex : toLex
            (metricRootCut i x,
              toLex (priority, metricSideRank x)) <
          toLex
            (metricRootCut i y,
              toLex (priority, metricSideRank y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hRank⟩)⟩)
        simpa only [metricSideKey, dif_neg hRootX,
          dif_neg hRootY] using hLex

/-- The key on the identified-base carrier, with one literal root
tag and two disjoint off-root sorts. -/
private noncomputable def metricRootedOrderKey
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [Fintype U] [Fintype V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V) :
    MetricRootedAmalgamVertex iU iV → ℕ ×ₗ (ℕ ×ₗ ℕ)
  | .inl a => metricSideKey iU 0 (iU a)
  | .inr (.inl x) => metricSideKey iU 0 x.val
  | .inr (.inr y) => metricSideKey iV 1 y.val

private theorem metricRootedOrderKey_left
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [Fintype U] [Fintype V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (p : A ⊕ MetricOutsideRoot iU) :
    metricRootedOrderKey iU iV (metricLeftSideIntoRooted iU iV p) =
      metricSideKey iU 0 ((metricSideEquiv iU
        (by
          intro a b hab
          exact a == b)).toFun p) := by
  sorry

end AllThoseRamseyClasses.Applications.MetricSaturation
