import AllThoseRamseyClasses.Applications.MetricEmptyBaseAmalgamation
import AllThoseRamseyClasses.Applications.MetricBlockConvexity
import Mathlib.Order.Sum.Order

/-!
# Empty-root amalgamation preserves the paper's metric block order

The separated metric sum constructed in `MetricEmptyBaseAmalgamation`
already preserves each original S-metric and gives every cross-side
pair the MAXIMAL S-distance m. This module provides the previously
missing **order part** of the empty-root gluing case.

Equip the disjoint union with the genuine old-left-before-old-right
linear SUM order, retaining both side orders exactly. No proper jump
j can relate vertices on opposite sides because j < m. Thus each
proper-jump equivalence class stays in one summand, and convexity
of the original side orders proves convexity of the amalgam.

For finite positive four-values S, the verified identification of
the paper's maximal-no-jump-block convexity with jump convexity
also yields the full PAPER block-convexity property of the glued
metric. Both the empty U and empty V cases are included.

This closes the **ordered empty-base case** only. Nonempty-base
shortest-path gluing, simultaneous completion of nested closure
functions, strong AP of the full metric lift and the metric Ramsey
theorem remain separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- The actual old-left-first, old-right-second lexicographic linear
sum of two genuine linear orders. This choice preserves both source
orders and never interleaves the summands. -/
noncomputable def separatedSumLexOrder
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V] :
    LinearOrder (Lex (U ⊕ V)) := inferInstance

/-- Transport that lexicographic sum order onto the ordinary
`U ⊕ V` carrier on which the separated metric is defined. -/
noncomputable def separatedSumLinearOrder
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V] :
    LinearOrder (U ⊕ V) :=
  @LinearOrder.lift' (U ⊕ V) (Lex (U ⊕ V))
    separatedSumLexOrder (toLex : U ⊕ V → Lex (U ⊕ V))
    toLex.injective

/-- The new order is definitionally the pullback of the intended
lexicographic sum order; use the named instance on BOTH sides to
avoid accidentally selecting the direct non-lex sum order. -/
theorem separatedSumLinearOrder_le_iff
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (a b : U ⊕ V) :
    @LE.le (U ⊕ V) (separatedSumLinearOrder (U := U) (V := V)).toLE a b ↔
      @LE.le (Lex (U ⊕ V))
        (separatedSumLexOrder (U := U) (V := V)).toLE
        (toLex a) (toLex b) := by
  change
    (@LinearOrder.lift' (U ⊕ V) (Lex (U ⊕ V))
      (separatedSumLexOrder (U := U) (V := V))
      (toLex : U ⊕ V → Lex (U ⊕ V))
      toLex.injective).le a b ↔
    @LE.le (Lex (U ⊕ V))
      (separatedSumLexOrder (U := U) (V := V)).toLE
      (toLex a) (toLex b)
  rfl

/-- The left summand retains its complete original linear order. -/
theorem separatedSumLinearOrder_inl_le_inl_iff
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (a b : U) :
    @LE.le (U ⊕ V) (separatedSumLinearOrder (U := U) (V := V)).toLE
      (.inl a) (.inl b) ↔ a ≤ b := by
  letI : LinearOrder (Lex (U ⊕ V)) := separatedSumLexOrder
  exact (separatedSumLinearOrder_le_iff (Sum.inl a : U ⊕ V)
    (Sum.inl b)).trans Sum.Lex.inl_le_inl_iff

/-- The right summand retains its complete original linear order. -/
theorem separatedSumLinearOrder_inr_le_inr_iff
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (a b : V) :
    @LE.le (U ⊕ V) (separatedSumLinearOrder (U := U) (V := V)).toLE
      (.inr a) (.inr b) ↔ a ≤ b := by
  letI : LinearOrder (Lex (U ⊕ V)) := separatedSumLexOrder
  exact (separatedSumLinearOrder_le_iff (Sum.inr a : U ⊕ V)
    (Sum.inr b)).trans Sum.Lex.inr_le_inr_iff

/-- No right-side vertex is before any left-side vertex in the
concatenated order. -/
theorem separatedSumLinearOrder_not_inr_le_inl
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (a : V) (b : U) :
    ¬ @LE.le (U ⊕ V) (separatedSumLinearOrder (U := U) (V := V)).toLE
      (.inr a) (.inl b) := by
  letI : LinearOrder (Lex (U ⊕ V)) := separatedSumLexOrder
  intro h
  have hh := (separatedSumLinearOrder_le_iff (Sum.inr a : U ⊕ V)
    (Sum.inl b)).mp h
  exact (Sum.Lex.not_inr_le_inl hh)

/-- Empty-base metric gluing preserves convexity at EVERY proper jump,
not just metric distances: a j-class cannot cross the summands and
the concatenated order cannot insert a right vertex between two left
ones (or conversely). -/
theorem separatedSumDistance_jumpConvex
    {S : Set ℝ}
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (m : ℝ) (hmax : ∀ s ∈ S, s ≤ m)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hU : JumpConvex S dU)
    (hV : JumpConvex S dV) :
    (letI := separatedSumLinearOrder (U := U) (V := V);
      JumpConvex S (separatedSumDistance m dU dV)) := by
  letI : LinearOrder (U ⊕ V) := separatedSumLinearOrder
  intro j hj a b c hab hbc hac
  cases a with
  | inl a =>
    cases c with
    | inl c =>
      cases b with
      | inl b =>
        have hab' := (separatedSumLinearOrder_inl_le_inl_iff
          (U := U) (V := V) a b).mp hab
        have hbc' := (separatedSumLinearOrder_inl_le_inl_iff
          (U := U) (V := V) b c).mp hbc
        exact hU j hj a b c hab' hbc' hac
      | inr b =>
        exact False.elim (separatedSumLinearOrder_not_inr_le_inl
          (U := U) (V := V) b c hbc)
    | inr c =>
      exact False.elim (separated_cross_not_jump
        m j hmax hj dU dV a c hac)
  | inr a =>
    cases c with
    | inl c =>
      have hAC : (Sum.inr a : U ⊕ V) ≤ Sum.inl c :=
        hab.trans hbc
      exact False.elim (separatedSumLinearOrder_not_inr_le_inl
        (U := U) (V := V) a c hAC)
    | inr c =>
      cases b with
      | inl b =>
        exact False.elim (separatedSumLinearOrder_not_inr_le_inl
          (U := U) (V := V) a b hab)
      | inr b =>
        have hab' := (separatedSumLinearOrder_inr_le_inr_iff
          (U := U) (V := V) a b).mp hab
        have hbc' := (separatedSumLinearOrder_inr_le_inr_iff
          (U := U) (V := V) b c).mp hbc
        exact hV j hj a b c hab' hbc' hac

/-- For finite four-values S, the concatenated disjoint-union metric
also preserves the manuscript's LITERAL maximal-no-jump block
convexity. This is the complete ORDERED empty-root case, not merely
the earlier standalone metric-distance amalgam. -/
theorem separatedSumDistance_paperBlockConvex
    {S : Set ℝ}
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (hfin : S.Finite) (hpos : Positive S)
    (h4 : FourValues S)
    (m : ℝ) (hm : m ∈ S) (hmax : ∀ s ∈ S, s ≤ m)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hU : PaperBlockConvex S dU)
    (hV : PaperBlockConvex S dV) :
    (letI := separatedSumLinearOrder (U := U) (V := V);
      PaperBlockConvex S (separatedSumDistance m dU dV)) := by
  letI : LinearOrder (U ⊕ V) := separatedSumLinearOrder
  have hJU : JumpConvex S dU :=
    (paperBlockConvex_iff_jumpConvex hfin hpos h4 hdU).mp hU
  have hJV : JumpConvex S dV :=
    (paperBlockConvex_iff_jumpConvex hfin hpos h4 hdV).mp hV
  have hMetric : MetricOn S (separatedSumDistance m dU dV) :=
    separatedSumDistance_metric hpos m hm hmax hdU hdV
  have hJump : JumpConvex S (separatedSumDistance m dU dV) :=
    separatedSumDistance_jumpConvex m hmax hJU hJV
  exact (paperBlockConvex_iff_jumpConvex hfin hpos h4 hMetric).mpr hJump

end AllThoseRamseyClasses.Applications.MetricSaturation
