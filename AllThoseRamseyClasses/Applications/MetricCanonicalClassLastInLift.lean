import AllThoseRamseyClasses.Applications.MetricCanonicalInsertionOrder
import AllThoseRamseyClasses.Applications.MetricCanonicalLiftThresholds

/-!
# The canonical closure representative is last in its completed jump class

The metric lift has one new vertex (j,E) for every original
positive-jump equivalence class E. The verified canonical metric
identifies exactly which ORIGINAL and CLOSURE vertices belong to
the completed j-equivalence class of (j,E).

This file proves that every one of those vertices is at most (j,E)
in the canonical insertion order, including closure vertices at
smaller jump levels. The argument has no global induction on jumps.

This supplies the 'last closure representative' direction of the
published lift's ordered functional class axiom. Interval convexity,
order preservation under embeddings, and strong amalgamation remain
separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- An original vertex at or before the last original member
of a jump class occurs strictly before the new closure vertex. -/
theorem canonicalInsertion_original_lt_tag_of_le_last {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) (x : V)
    (hx : x ≤ canonicalClassLast hpos hS hd tag) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inl x : V ⊕ CanonicalJumpTag hpos hS hd) <
        Sum.inr tag) := by
  change toLex ((x, none) : V × WithBot ℝ) <
    toLex ((canonicalClassLast hpos hS hd tag,
      some (canonicalTagLevel tag)) : V × WithBot ℝ)
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    simpa only [WithBot.none_eq_bot, WithBot.some_eq_coe] using
      (WithBot.bot_lt_coe (canonicalTagLevel tag))

/-- Strictly increasing last-original anchors put the entire
earlier closure class before the later closure representative. -/
theorem canonicalInsertion_tag_lt_tag_of_last_lt {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd)
    (hanchor : canonicalClassLast hpos hS hd a <
      canonicalClassLast hpos hS hd b) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inr a : V ⊕ CanonicalJumpTag hpos hS hd) <
        Sum.inr b) := by
  change toLex ((canonicalClassLast hpos hS hd a,
      some (canonicalTagLevel a)) : V × WithBot ℝ) <
    toLex ((canonicalClassLast hpos hS hd b,
      some (canonicalTagLevel b)) : V × WithBot ℝ)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl hanchor

/-- Every vertex in the completed j-threshold class of
the canonical closure tag (j,E) lies before or at that tag
in the checked lexicographic insertion order.

In particular, a lower-jump closure vertex within E is
not accidentally placed after the enclosing j-closure.
-/
theorem canonicalInsertion_closure_last_of_threshold {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd)
    (y : V ⊕ CanonicalJumpTag hpos hS hd)
    (hy : canonicalDistance hpos hS hd (.inr tag) y ≤
      canonicalTagLevel tag) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      y ≤ (Sum.inr tag : V ⊕ CanonicalJumpTag hpos hS hd)) := by
  cases y with
  | inl x =>
      have hparts :=
        (canonicalDistance_closure_old_le_jump_iff hpos hS
          hd tag x (canonicalTagLevel_jump tag)).mp hy
      have hx : d x (canonicalTagRoot tag) ≤
          canonicalTagLevel tag := by
        rw [hd.symm x (canonicalTagRoot tag)]
        exact hparts.2
      have hle := canonicalClassLast_max hpos hS hd tag x hx
      exact le_of_lt
        (canonicalInsertion_original_lt_tag_of_le_last hpos hS hd tag x hle)
  | inr other =>
      by_cases heq : other = tag
      · subst other
        exact le_refl _
      · have hparts :=
          (canonicalDistance_closure_closure_le_jump_iff
            hpos hS hd tag other (Ne.symm heq)
            (canonicalTagLevel_jump tag)).mp hy
        have hlevel : canonicalTagLevel other ≤
            canonicalTagLevel tag := hparts.2.2
        have hroot : d (canonicalTagRoot other)
            (canonicalTagRoot tag) ≤ canonicalTagLevel tag := by
          rw [hd.symm (canonicalTagRoot other) (canonicalTagRoot tag)]
          exact hparts.2.1
        have hlastmem := canonicalClassLast_mem hpos hS hd other
        have hclose :
            d (canonicalClassLast hpos hS hd other)
              (canonicalTagRoot tag) ≤ canonicalTagLevel tag :=
          metric_jump_threshold_trans hpos hS hd
            (Or.inr (canonicalTagLevel_jump tag))
            (canonicalClassLast hpos hS hd other)
            (canonicalTagRoot other) (canonicalTagRoot tag)
            (hlastmem.trans hlevel) hroot
        have hanchor : canonicalClassLast hpos hS hd other ≤
            canonicalClassLast hpos hS hd tag :=
          canonicalClassLast_max hpos hS hd tag
            (canonicalClassLast hpos hS hd other) hclose
        rcases lt_or_eq_of_le hanchor with hlt | hanchoreq
        · exact le_of_lt
            (canonicalInsertion_tag_lt_tag_of_last_lt
              hpos hS hd other tag hlt)
        · rcases lt_or_eq_of_le hlevel with hlevelLt | hlevelEq
          · exact le_of_lt
              (canonicalInsertion_increasing_levels hpos hS hd
                other tag hanchoreq hlevelLt)
          · exact False.elim (heq
              (canonicalTag_eq_of_level_last hpos hS hd
                other tag hlevelEq hanchoreq))

end AllThoseRamseyClasses.Applications.MetricSaturation
