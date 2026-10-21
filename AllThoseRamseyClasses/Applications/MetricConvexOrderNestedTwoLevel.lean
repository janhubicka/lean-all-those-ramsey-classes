import AllThoseRamseyClasses.Applications.MetricConvexOrderRefinement

/-!
# Both levels of a nested class-label order are convex

For a two-level lexicographic key (coarse class, fine class,
original vertex), the coarser class is always an interval.
The finer class is also an interval if it determines its
coarser class. Old comparisons survive if the coarse label
is monotone and the fine label is monotone within coarse classes.

This is an interface for iterating the construction over
all finite S-metric jump levels. It does not yet construct
compatible labels on the amalgamated metric.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w

/-- Old comparisons survive sorting by coarse, then fine, then
the original order, if these class keys do not decrease. -/
theorem nestedLabelOrder_strict_of_mono
    {X : Type u} {C : Type v} {F : Type w}
    [LinearOrder X] [LinearOrder C] [LinearOrder F]
    (coarse : X → C) (fine : X → F)
    {x y : X} (hxy : x < y)
    (hcoarse : coarse x ≤ coarse y)
    (hfine : coarse x = coarse y → fine x ≤ fine y) :
    @LT.lt X (nestedLabelOrder coarse fine).toLT x y := by
  change
    @LT.lt X
      (labelFirstOrder
        (fun t : X => (toLex (coarse t, fine t) : C ×ₗ F))).toLT x y
  apply (labelFirst_lt_iff
    (fun t : X => (toLex (coarse t, fine t) : C ×ₗ F)) x y).mpr
  rcases lt_or_eq_of_le hcoarse with hc | hc
  · exact Or.inl (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hc))
  · rcases lt_or_eq_of_le (hfine hc) with hf | hf
    · exact Or.inl
        (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hc, hf⟩))
    · refine Or.inr ⟨?_, hxy⟩
      exact congrArg (fun t : C × F => (toLex t : C ×ₗ F))
        (Prod.ext hc hf)

/-- Under nestedness, the coarse and fine classes are BOTH
convex in exactly the same two-level linear order. -/
theorem nestedLabelOrder_both_convex
    {X : Type u} {C : Type v} {F : Type w}
    [LinearOrder X] [LinearOrder C] [LinearOrder F]
    (coarse : X → C) (fine : X → F)
    (hNested : ∀ x y : X,
      fine x = fine y → coarse x = coarse y) :
    (∀ x y z : X,
      @LE.le X (nestedLabelOrder coarse fine).toLE x y →
      @LE.le X (nestedLabelOrder coarse fine).toLE y z →
      coarse x = coarse z → coarse x = coarse y) ∧
    (∀ x y z : X,
      @LE.le X (nestedLabelOrder coarse fine).toLE x y →
      @LE.le X (nestedLabelOrder coarse fine).toLE y z →
      fine x = fine z → fine x = fine y) := by
  constructor
  · intro x y z hxy hyz hc
    exact nestedLabelOrder_coarse_convex coarse fine x y z hxy hyz hc
  · intro x y z hxy hyz hf
    exact nestedLabelOrder_fine_convex
      coarse fine hNested x y z hxy hyz hf

end AllThoseRamseyClasses.Applications.MetricConvexOrder
