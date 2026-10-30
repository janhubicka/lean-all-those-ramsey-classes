import AllThoseRamseyClasses.Applications.MetricBlockPathAbsorption
import Mathlib.Tactic

/-!
# Replace a constant rounded-prefix path in its actual outer context

The printed `lem:Sequivalence` replaces disjoint unimportant
paths INSIDE the opposite side of a nonmetric cycle. It is not
enough to verify the rounded length of each replacement in
isolation: replacing a middle path must leave the rounded
length of the entire opposite path unchanged, including
the later suffix.

This is a general fold-congruence statement. If the old and
new middle segments have equal folds from the prefix reached
by the common preceding segment, appending the same suffix
preserves equality. It immediately applies to a plateau,
where both middle folds return the attained prefix.

By repeating this exact contextual substitution, an arbitrary
finite sequence of disjoint segment replacements preserves
the final prefix, provided each segment's local plateau and
replacement bounds are certified. The actual choice/geometry
of those disjoint segments is not provided here.

No strengthened completion, metric or Ramsey claim is made.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Replacement of one arbitrary contiguous LIST segment preserves
the overall fold as soon as the two middle folds agree from the
prefix state reached by the common initial segment. This is
independent of metric laws or positivity. -/
theorem foldl_replace_middle_in_context
    {α : Type u} {β : Type v}
    (f : β → α → β)
    (start : β)
    (before old new after : List α)
    (hMid : old.foldl f (before.foldl f start) =
      new.foldl f (before.foldl f start)) :
    (before ++ old ++ after).foldl f start =
      (before ++ new ++ after).foldl f start := by
  simp only [List.foldl_append]
  rw [hMid]

/-- The exact unimportant-path form: both the original and
replacement middle path return the same attained prefix a. -/
theorem roundedPlateau_replace_middle
    (S : Set ℝ)
    (start a : ℝ)
    (before old replacement after : List ℝ)
    (hBefore : before.foldl (distanceSum S) start = a)
    (hOld : old.foldl (distanceSum S) a = a)
    (hNew : replacement.foldl (distanceSum S) a = a) :
    (before ++ old ++ after).foldl (distanceSum S) start =
      (before ++ replacement ++ after).foldl (distanceSum S) start := by
  apply foldl_replace_middle_in_context (distanceSum S)
    start before old replacement after
  rw [hBefore, hOld, hNew]

/-- A strict incompatibility with the final closing edge remains
strictly incompatible after any such contextual plateau
replacement, without recomputing any later path lengths. -/
theorem roundedPlateau_replace_middle_preserves_bad
    (S : Set ℝ)
    (start a d : ℝ)
    (before old replacement after : List ℝ)
    (hBefore : before.foldl (distanceSum S) start = a)
    (hOld : old.foldl (distanceSum S) a = a)
    (hNew : replacement.foldl (distanceSum S) a = a)
    (hBad : (before ++ old ++ after).foldl
      (distanceSum S) start < d) :
    (before ++ replacement ++ after).foldl
      (distanceSum S) start < d := by
  rw [← roundedPlateau_replace_middle
    S start a before old replacement after hBefore hOld hNew]
  exact hBad

end AllThoseRamseyClasses.Applications.MetricSaturation
