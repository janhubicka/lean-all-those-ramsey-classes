import AllThoseRamseyClasses.Applications.MetricConvexOrderRefinement

/-!
# Preserve nested convex class fibres under a coarser refinement

There is no need to encode an entire finite hierarchy of metric jump
classes by one enormous lexicographic tuple. A simpler iterative
construction processes its jump levels from FINE to COARSE.

Given a linear order in which the fibres of a fine class label
already form intervals, and a coarser label constant on each
fine fibre, sorting all vertices by the COARSER label first
preserves the finer intervals, while making every coarser
fibre an interval as well.

The proof is purely finite-order combinatorics and makes no
metric assumption. It is the induction invariant for turning
the verified strong metric pushout and its exact nested
jump-class decomposition into one simultaneously convex order.
Compatibility of class orders across the two original metric
sides and auxiliary F_j amalgamation remain separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w

/-- A label is convex in an explicitly supplied linear order
when every fibre is an interval. The label carrier needs no
ordering of its own. -/
def FibreConvex
    {X : Type u} (o : LinearOrder X)
    {K : Type v} (label : X → K) : Prop :=
  ∀ x y z : X,
    @LE.le X o.toLE x y →
    @LE.le X o.toLE y z →
    label x = label z → label x = label y

/-- If two vertices have the SAME class label, their
comparison in the label-first refined order is exactly
their comparison in the underlying original order. -/
theorem labelFirst_le_old_of_label_eq
    {X : Type u} {K : Type v}
    [LinearOrder X] [LinearOrder K]
    (label : X → K) {x y : X}
    (hxy : @LE.le X (labelFirstOrder label).toLE x y)
    (heq : label x = label y) :
    x ≤ y := by
  by_contra hn
  have hyx : y < x := lt_of_not_ge hn
  have hnew :
      @LT.lt X (labelFirstOrder label).toLT y x :=
    (labelFirst_lt_iff label y x).mpr
      (Or.inr ⟨heq.symm, hyx⟩)
  exact (not_lt_of_ge hxy) hnew

/-- Class fibre convexity holds for the newly introduced
coarse labels by the direct lexicographic order. -/
theorem labelFirst_coarse_fibre_convex
    {X : Type u} {C : Type v}
    [LinearOrder X] [LinearOrder C]
    (coarse : X → C) :
    FibreConvex (labelFirstOrder coarse) coarse := by
  intro x y z hxy hyz hc
  exact labelFirst_fibre_convex coarse x y z hxy hyz hc

/-- KEY FINITE-HIERARCHY INVARIANT:
Refining an order by a coarser class label retains convexity
of each previously convex finer class, if a finer class is
contained in exactly one coarser class.

This is strictly more reusable than a special two-level tuple:
the theorem may be applied repeatedly through an arbitrary
finite sequence of increasingly coarser jump thresholds. -/
theorem labelFirst_preserves_nested_fibre_convex
    {X : Type u} {C : Type v} {F : Type w}
    [LinearOrder X] [LinearOrder C]
    (coarse : X → C) (fine : X → F)
    (hNested : ∀ x y : X,
      fine x = fine y → coarse x = coarse y)
    (hFine : FibreConvex (inferInstance : LinearOrder X) fine) :
    FibreConvex (labelFirstOrder coarse) fine := by
  intro x y z hxy hyz hf
  have hcXZ : coarse x = coarse z := hNested x z hf
  have hcXY : coarse x = coarse y :=
    labelFirst_fibre_convex coarse x y z hxy hyz hcXZ
  have hcYZ : coarse y = coarse z := hcXY.symm.trans hcXZ
  have hOldXY : x ≤ y :=
    labelFirst_le_old_of_label_eq coarse hxy hcXY
  have hOldYZ : y ≤ z :=
    labelFirst_le_old_of_label_eq coarse hyz hcYZ
  exact hFine x y z hOldXY hOldYZ hf

/-- A single refinement simultaneously establishes convexity
of the NEW coarser classes and preserves convexity of the
ALREADY completed finer classes. This supplies exactly the
one-step invariant for a finite-jump induction. -/
theorem labelFirst_refinement_both_convex
    {X : Type u} {C : Type v} {F : Type w}
    [LinearOrder X] [LinearOrder C]
    (coarse : X → C) (fine : X → F)
    (hNested : ∀ x y : X,
      fine x = fine y → coarse x = coarse y)
    (hFine : FibreConvex (inferInstance : LinearOrder X) fine) :
    FibreConvex (labelFirstOrder coarse) coarse ∧
      FibreConvex (labelFirstOrder coarse) fine :=
  ⟨labelFirst_coarse_fibre_convex coarse,
   labelFirst_preserves_nested_fibre_convex coarse fine hNested hFine⟩

end AllThoseRamseyClasses.Applications.MetricConvexOrder
