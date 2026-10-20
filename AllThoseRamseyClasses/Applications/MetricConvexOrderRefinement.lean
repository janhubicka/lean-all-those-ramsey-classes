import Mathlib.Order.Prod.Lex.Basic

/-!
# A reusable convex-class refinement of an existing finite order

The canonical-rooted metric amalgam already has an ordinary
linear order preserving both side orders. This module isolates
the strictly simpler NEXT step: if a class label can be ordered
monotonically along both old sides, sorting by that label FIRST
and the old vertex order SECOND preserves both side orders
while making every label class an interval.

The result works without finiteness or metric hypotheses.
The two-level version formalizes the nesting principle:
if finer classes determine their coarser class, sorting by the
pair of labels also keeps finer classes convex.

This is an *interface* for recursive amalgamation of the
finite nested jump equivalences; it does not construct the
metric class labels or their compatible orders, and it does
not certify the final jump-convex metric amalgamation.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w

/-- Sort by a class label first, with the original order as
the injective within-class tie breaker. This is a genuine
linear order on the very same carrier. -/
noncomputable def labelFirstOrder
    {X : Type u} {K : Type v}
    [LinearOrder X] [LinearOrder K]
    (label : X → K) : LinearOrder X :=
  LinearOrder.lift'
    (fun x : X => toLex (label x, x))
    (by
      intro x y h
      exact congrArg (fun t : K ×ₗ X => (ofLex t).2) h)

/-- Exact strict comparison in the new lexicographic order. -/
theorem labelFirst_lt_iff
    {X : Type u} {K : Type v}
    [LinearOrder X] [LinearOrder K]
    (label : X → K) (x y : X) :
    @LT.lt X (labelFirstOrder label).toLT x y ↔
      label x < label y ∨
        (label x = label y ∧ x < y) := by
  change (toLex (label x, x) : K ×ₗ X) <
    toLex (label y, y) ↔ _
  exact Prod.Lex.toLex_lt_toLex

/-- Any old increasing comparison remains strict in the refined
order if its class label does not go backwards. This is the
side-order preservation lemma required for amalgamation. -/
theorem labelFirst_strict_of_label_mono
    {X : Type u} {K : Type v}
    [LinearOrder X] [LinearOrder K]
    (label : X → K) {x y : X}
    (hxy : x < y) (hlabel : label x ≤ label y) :
    @LT.lt X (labelFirstOrder label).toLT x y := by
  apply (labelFirst_lt_iff label x y).mpr
  rcases lt_or_eq_of_le hlabel with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hxy⟩

/-- Every fibre of the class-label map is an interval in the
refined linear order. In particular this is the elementary
convexity invariant for one level of an equivalence hierarchy. -/
theorem labelFirst_fibre_convex
    {X : Type u} {K : Type v}
    [LinearOrder X] [LinearOrder K]
    (label : X → K) (x y z : X)
    (hxy : @LE.le X (labelFirstOrder label).toLE x y)
    (hyz : @LE.le X (labelFirstOrder label).toLE y z)
    (hxz : label x = label z) :
    label x = label y := by
  letI : LinearOrder X := labelFirstOrder label
  have hxy' : x ≤ y := hxy
  have hyz' : y ≤ z := hyz
  have hleXY : label x ≤ label y := by
    by_contra h
    have hyx : label y < label x := lt_of_not_ge h
    have hnew : y < x :=
      (labelFirst_lt_iff label y x).mpr (Or.inl hyx)
    exact (not_lt_of_ge hxy') hnew
  have hleYZ : label y ≤ label z := by
    by_contra h
    have hzy : label z < label y := lt_of_not_ge h
    have hnew : z < y :=
      (labelFirst_lt_iff label z y).mpr (Or.inl hzy)
    exact (not_lt_of_ge hyz') hnew
  have hleYX : label y ≤ label x := by
    calc
      label y ≤ label z := hleYZ
      _ = label x := hxz.symm
  exact le_antisymm hleXY hleYX

/-- Two nested levels can be represented as a single
lexicographically ordered pair of class labels. -/
noncomputable def nestedLabelOrder
    {X : Type u} {C : Type v} {F : Type w}
    [LinearOrder X] [LinearOrder C] [LinearOrder F]
    (coarse : X → C) (fine : X → F) : LinearOrder X :=
  labelFirstOrder
    (fun x : X => (toLex (coarse x, fine x) : C ×ₗ F))

/-- The finest fibres stay intervals when a fine-class label
determines its coarser-class label. This avoids assuming that
arbitrary independent partitions have convex common refinements. -/
theorem nestedLabelOrder_fine_convex
    {X : Type u} {C : Type v} {F : Type w}
    [LinearOrder X] [LinearOrder C] [LinearOrder F]
    (coarse : X → C) (fine : X → F)
    (hNested : ∀ x y : X, fine x = fine y → coarse x = coarse y)
    (x y z : X)
    (hxy : @LE.le X (nestedLabelOrder coarse fine).toLE x y)
    (hyz : @LE.le X (nestedLabelOrder coarse fine).toLE y z)
    (hf : fine x = fine z) :
    fine x = fine y := by
  let label : X → C ×ₗ F :=
    fun t => toLex (coarse t, fine t)
  have hEq : label x = label z := by
    dsimp [label]
    rw [hNested x z hf, hf]
  have hLabels : label x = label y :=
    labelFirst_fibre_convex label x y z hxy hyz hEq
  exact congrArg (fun t : C ×ₗ F => (ofLex t).2) hLabels

end AllThoseRamseyClasses.Applications.MetricConvexOrder
