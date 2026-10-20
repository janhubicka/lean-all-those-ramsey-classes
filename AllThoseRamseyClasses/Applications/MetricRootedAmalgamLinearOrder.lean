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
    (hiU : Function.Injective iU)
    (p : A ⊕ MetricOutsideRoot iU) :
    metricRootedOrderKey iU iV (metricLeftSideIntoRooted iU iV p) =
      metricSideKey iU 0 (metricSideEquiv iU hiU p) := by
  cases p with
  | inl a => rfl
  | inr x => rfl

private theorem metricRootedOrderKey_right
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [Fintype U] [Fintype V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (hCompat : ∀ a b : A, iU a < iU b ↔ iV a < iV b)
    (p : A ⊕ MetricOutsideRoot iV) :
    metricRootedOrderKey iU iV (metricRightSideIntoRooted iU iV p) =
      metricSideKey iV 1 (metricSideEquiv iV hiV p) := by
  cases p with
  | inl a => exact metricSideKey_root_agree iU iV hCompat a
  | inr y => rfl

private theorem metricRootedOrderKey_of_left
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [Fintype U] [Fintype V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (x : U) :
    metricRootedOrderKey iU iV (metricRootedLeft iU iV hiU x) =
      metricSideKey iU 0 x := by
  unfold metricRootedLeft
  rw [metricRootedOrderKey_left iU iV hiU
      ((metricSideEquiv iU hiU).symm x),
    (metricSideEquiv iU hiU).apply_symm_apply x]

private theorem metricRootedOrderKey_of_right
    {A : Type u} {U : Type v} {V : Type w}
    [Fintype A] [Fintype U] [Fintype V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV)
    (hCompat : ∀ a b : A, iU a < iU b ↔ iV a < iV b)
    (y : V) :
    metricRootedOrderKey iU iV (metricRootedRight iU iV hiV y) =
      metricSideKey iV 1 y := by
  unfold metricRootedRight
  rw [metricRootedOrderKey_right iU iV hiV hCompat
      ((metricSideEquiv iV hiV).symm y),
    (metricSideEquiv iV hiV).apply_symm_apply y]

/-- A linear order exists on the EXACT identified-base metric
pushout, preserving both original side orders. This is the
plain ordered-amalgam component; metric jump-convexity is NOT
part of the conclusion. -/
theorem metricRootedLinearOrder_exists
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    (hCompat : ∀ a b : A, iU a < iU b ↔ iV a < iV b) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiU x)
          (metricRootedLeft iU iV hiU y)) ∧
      (∀ x y : V, x < y →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiV x)
          (metricRootedRight iU iV hiV y)) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  let P := MetricRootedAmalgamVertex iU iV
  letI : Finite P := metricRootedAmalgamVertex_finite iU iV
  letI : Fintype P := Fintype.ofFinite P
  let key : P → (ℕ ×ₗ (ℕ ×ₗ ℕ)) ×ₗ Fin (Fintype.card P) :=
    fun x => toLex (metricRootedOrderKey iU iV x, Fintype.equivFin P x)
  have hKeyInj : Function.Injective key := by
    intro x y hxy
    apply (Fintype.equivFin P).injective
    exact congrArg (fun t => (ofLex t).2) hxy
  let o : LinearOrder P := LinearOrder.lift' key hKeyInj
  refine ⟨o, ?_, ?_⟩
  · intro x y hxy
    have hSide : metricSideKey iU 0 x < metricSideKey iU 0 y :=
      metricSideKey_strict iU 0 (by omega) hxy
    have hMerged :
        metricRootedOrderKey iU iV (metricRootedLeft iU iV hiU x) <
        metricRootedOrderKey iU iV (metricRootedLeft iU iV hiU y) := by
      rw [metricRootedOrderKey_of_left iU iV hiU x,
          metricRootedOrderKey_of_left iU iV hiU y]
      exact hSide
    change key (metricRootedLeft iU iV hiU x) <
      key (metricRootedLeft iU iV hiU y)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hMerged)
  · intro x y hxy
    have hSide : metricSideKey iV 1 x < metricSideKey iV 1 y :=
      metricSideKey_strict iV 1 (by omega) hxy
    have hMerged :
        metricRootedOrderKey iU iV (metricRootedRight iU iV hiV x) <
        metricRootedOrderKey iU iV (metricRootedRight iU iV hiV y) := by
      rw [metricRootedOrderKey_of_right iU iV hiV hCompat x,
          metricRootedOrderKey_of_right iU iV hiV hCompat y]
      exact hSide
    change key (metricRootedRight iU iV hiV x) <
      key (metricRootedRight iU iV hiV y)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hMerged)

end AllThoseRamseyClasses.Applications.MetricSaturation
