import AllThoseRamseyClasses.Applications.MetricCanonicalClassLast
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.WithBot

/-!
# Faithful finite linear order for canonical metric closure vertices

The original vertices retain their prescribed linear order. For each
positive jump-class tag we attach a closure vertex after the *last
original member* of that class. If several closure levels have that
same last original vertex, sort the added vertices by *increasing*
jump level: the higher-level closure then lies after all lower-level
ones, including those previously inserted.

The lexicographic insertion key for an original x is (x, none);
for a closure tag (j,E) it is (last(E), some j). The key is
injective: its first component distinguishes old original
vertices, the second distinguishes old from new and jump
levels, and the checked class-last theorem says a class is
uniquely determined by its level and last member.

This produces an honest linear order of the exact duplicate-free
carrier. Its compatibility with the paper's full block-convexity
on the *extended metric* and functorial order preservation are
separate proof obligations, not assumptions of this module.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Lexicographic insertion key on the canonical closure carrier.
The option-none key places an old original vertex before all new
closure representatives with the same last original anchor. -/
noncomputable def canonicalInsertionKey {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    (V ⊕ CanonicalJumpTag hpos hS hd) → Lex (V × WithBot ℝ)
  | .inl x => toLex (x, none)
  | .inr tag =>
      toLex (canonicalClassLast hpos hS hd tag,
        some (canonicalTagLevel tag))

/-- There are no collisions of insertion keys. In particular
there cannot be two different tags at the same jump level
anchored after the same last original vertex. -/
theorem canonicalInsertionKey_injective {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    Function.Injective (canonicalInsertionKey hpos hS hd) := by
  intro a b h
  have heq := congrArg
    (ofLex : Lex (V × WithBot ℝ) → V × WithBot ℝ) h
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          have hxy : x = y := by
            simpa [canonicalInsertionKey] using congrArg Prod.fst heq
          cases hxy
          rfl
      | inr tag =>
          have hc : (none : WithBot ℝ) =
              some (canonicalTagLevel tag) := by
            simpa [canonicalInsertionKey] using congrArg Prod.snd heq
          cases hc
  | inr tag =>
      cases b with
      | inl y =>
          have hc : (some (canonicalTagLevel tag) : WithBot ℝ) =
              none := by
            simpa [canonicalInsertionKey] using congrArg Prod.snd heq
          cases hc
      | inr other =>
          have hlast : canonicalClassLast hpos hS hd tag =
              canonicalClassLast hpos hS hd other := by
            simpa [canonicalInsertionKey] using congrArg Prod.fst heq
          have hlevel : canonicalTagLevel tag =
              canonicalTagLevel other := by
            have hsome : (some (canonicalTagLevel tag) : WithBot ℝ) =
                some (canonicalTagLevel other) := by
              exact congrArg Prod.snd heq
            exact Option.some.inj hsome
          have htag := canonicalTag_eq_of_level_last
            hpos hS hd tag other hlevel hlast
          cases htag
          rfl

/-- Pull the standard lexicographic linear order back along the
injective insertion key, without choosing any arbitrary tie breaks.
This is a non-instance to avoid creating an unrelated global order
on all metric lifts. -/
noncomputable def canonicalInsertionLinearOrder {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    LinearOrder (V ⊕ CanonicalJumpTag hpos hS hd) := by
  classical
  exact LinearOrder.lift'
    (canonicalInsertionKey hpos hS hd)
    (canonicalInsertionKey_injective hpos hS hd)

/-- The insertion key of an old original vertex does not change
its position in the original linear order. -/
theorem canonicalInsertion_old_lt_iff {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) (x y : V) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inl x : V ⊕ CanonicalJumpTag hpos hS hd) <
        (Sum.inl y : V ⊕ CanonicalJumpTag hpos hS hd)) ↔ x < y := by
  change toLex ((x, none) : V × WithBot ℝ) <
      toLex ((y, none) : V × WithBot ℝ) ↔ x < y
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hlt | ⟨_, hnone⟩)
    · exact hlt
    · change WithBot.LT none none at hnone
      cases hnone
  · intro hlt
    exact Or.inl hlt

/-- A closure representative is strictly after the last original
member of its class in the extended linear order. -/
theorem canonicalInsertion_after_last {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inl (canonicalClassLast hpos hS hd tag) :
        V ⊕ CanonicalJumpTag hpos hS hd) < Sum.inr tag) := by
  change toLex
      ((canonicalClassLast hpos hS hd tag, none) : V × WithBot ℝ) <
    toLex
      ((canonicalClassLast hpos hS hd tag,
        some (canonicalTagLevel tag)) : V × WithBot ℝ)
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  simpa only [WithBot.none_eq_bot, WithBot.some_eq_coe] using
    (WithBot.bot_lt_coe (canonicalTagLevel tag))

/-- If two closure classes end at the same original vertex,
the closure vertex at the smaller jump level is inserted first. -/
theorem canonicalInsertion_increasing_levels {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd)
    (hlast : canonicalClassLast hpos hS hd a =
      canonicalClassLast hpos hS hd b)
    (hlevel : canonicalTagLevel a < canonicalTagLevel b) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inr a : V ⊕ CanonicalJumpTag hpos hS hd) <
        (Sum.inr b : V ⊕ CanonicalJumpTag hpos hS hd)) := by
  change toLex
      ((canonicalClassLast hpos hS hd a,
        some (canonicalTagLevel a)) : V × WithBot ℝ) <
    toLex
      ((canonicalClassLast hpos hS hd b,
        some (canonicalTagLevel b)) : V × WithBot ℝ)
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hlast, ?_⟩
  simpa only [WithBot.some_eq_coe, WithBot.coe_lt_coe] using hlevel

end AllThoseRamseyClasses.Applications.MetricSaturation
