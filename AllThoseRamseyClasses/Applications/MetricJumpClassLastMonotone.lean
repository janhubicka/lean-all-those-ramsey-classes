import AllThoseRamseyClasses.Applications.MetricJumpClassOrder
import Mathlib.Tactic

/-!
# Monotone class-last labels in convexly ordered finite S-metrics

At a fixed proper jump j, every j-equivalence class in a finite
linearly ordered metric space has a greatest member. This is a
concrete representative of the class, not a choice of an arbitrary
root or of a quotient set.

For a j-convex original order the map sending x to the greatest
member of its class is monotone. Two vertices have the SAME
class-last label exactly when they are j-equivalent.

Together with the generic label-first order-refinement lemma,
this gives a finite-order key for the child classes in the
nested metric amalgamation proof. It does not itself choose a
compatible order on the glued classes of two different spaces.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Every j-class has a last vertex in any finite original
metric order. Only j ∈ S and positivity are needed for
the class to contain its original root point. -/
theorem exists_metricJumpClassLast
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x : V) :
    ∃ m : V,
      d m x ≤ j ∧
      ∀ y : V, d y x ≤ j → y ≤ m := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let C : Finset V :=
    Finset.univ.filter (fun y => d y x ≤ j)
  have hC : C.Nonempty := by
    refine ⟨x, ?_⟩
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hd.diag x]
    exact (hpos j hj.1).le
  let m : V := C.max' hC
  refine ⟨m, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem C hC)).2
  · intro y hy
    apply Finset.le_max' C y
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩

/-- The greatest vertex of the j-class containing x. -/
noncomputable def metricJumpClassLast
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x : V) : V :=
  Classical.choose (exists_metricJumpClassLast hpos hd j hj x)

theorem metricJumpClassLast_mem
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x : V) :
    d (metricJumpClassLast hpos hd j hj x) x ≤ j :=
  (Classical.choose_spec
    (exists_metricJumpClassLast hpos hd j hj x)).1

theorem metricJumpClassLast_max
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x y : V)
    (hy : d y x ≤ j) :
    y ≤ metricJumpClassLast hpos hd j hj x :=
  (Classical.choose_spec
    (exists_metricJumpClassLast hpos hd j hj x)).2 y hy

/-- A j-close pair has the exact SAME last-class label.
The equality is justified by threshold transitivity, not
by assuming that arbitrary nearest roots are unique. -/
theorem metricJumpClassLast_eq_of_close
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x y : V)
    (hxy : d x y ≤ j) :
    metricJumpClassLast hpos hd j hj x =
      metricJumpClassLast hpos hd j hj y := by
  have hyx : d y x ≤ j := by
    rw [hd.symm y x]
    exact hxy
  apply le_antisymm
  · apply metricJumpClassLast_max hpos hd j hj y
    exact metric_jump_threshold_trans hpos hS hd (Or.inr hj)
      (metricJumpClassLast hpos hd j hj x) x y
      (metricJumpClassLast_mem hpos hd j hj x) hxy
  · apply metricJumpClassLast_max hpos hd j hj x
    exact metric_jump_threshold_trans hpos hS hd (Or.inr hj)
      (metricJumpClassLast hpos hd j hj y) y x
      (metricJumpClassLast_mem hpos hd j hj y) hyx

/-- Conversely, equality of last-class labels forces the
original vertices to be j-equivalent. No convexity needed. -/
theorem metricJumpClassLast_close_of_eq
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x y : V)
    (heq : metricJumpClassLast hpos hd j hj x =
      metricJumpClassLast hpos hd j hj y) :
    d x y ≤ j := by
  have hx : d x (metricJumpClassLast hpos hd j hj x) ≤ j := by
    rw [hd.symm x (metricJumpClassLast hpos hd j hj x)]
    exact metricJumpClassLast_mem hpos hd j hj x
  have hy : d (metricJumpClassLast hpos hd j hj y) y ≤ j :=
    metricJumpClassLast_mem hpos hd j hj y
  rw [← heq] at hy
  exact metric_jump_threshold_trans hpos hS hd (Or.inr hj)
    x (metricJumpClassLast hpos hd j hj x) y hx hy

/-- In an original j-convex order, the class-last label is
monotone. This is the key property needed when extending both
old orders by sorting all vertices by class first. -/
theorem metricJumpClassLast_mono
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (hconv : JumpConvex S d)
    (j : ℝ) (hj : Jump S j) :
    Monotone (metricJumpClassLast hpos hd j hj) := by
  intro x y hxy
  by_cases heq : x = y
  · subst y
    exact le_refl _
  have hlt : x < y := lt_of_le_of_ne hxy heq
  by_cases hClose : d x y ≤ j
  · exact le_of_eq
      (metricJumpClassLast_eq_of_close
        hpos hS hd j hj x y hClose)
  · have hmemX : d x (metricJumpClassLast hpos hd j hj x) ≤ j := by
      rw [hd.symm x (metricJumpClassLast hpos hd j hj x)]
      exact metricJumpClassLast_mem hpos hd j hj x
    have hmemY : d y (metricJumpClassLast hpos hd j hj y) ≤ j := by
      rw [hd.symm y (metricJumpClassLast hpos hd j hj y)]
      exact metricJumpClassLast_mem hpos hd j hj y
    exact le_of_lt
      (jumpConvex_disjoint_classes_order
        hpos hS hd hconv j hj
        x (metricJumpClassLast hpos hd j hj x)
        y (metricJumpClassLast hpos hd j hj y)
        hmemX hmemY hClose hlt)

/-- Taking the last member of a j-class twice changes nothing:
the selected maximum lies in the original threshold class. -/
theorem metricJumpClassLast_idempotent
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x : V) :
    metricJumpClassLast hpos hd j hj
        (metricJumpClassLast hpos hd j hj x) =
      metricJumpClassLast hpos hd j hj x :=
  metricJumpClassLast_eq_of_close hpos hS hd j hj
    (metricJumpClassLast hpos hd j hj x) x
    (metricJumpClassLast_mem hpos hd j hj x)

/-- Concrete finite representatives of the j-classes: precisely
the fixed points of the last-member map. They inherit the
original linear order, with no chosen quotient order. -/
abbrev MetricJumpClassRep
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) : Type u :=
  {x : V // metricJumpClassLast hpos hd j hj x = x}

/-- The actual j-class label of an original vertex, as a point
of the finite, linearly ordered class-representative carrier. -/
noncomputable def metricJumpClassTag
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x : V) :
    MetricJumpClassRep hpos hd j hj :=
  ⟨metricJumpClassLast hpos hd j hj x,
    metricJumpClassLast_idempotent hpos hS hd j hj x⟩

/-- Equality of canonical class representatives is equivalent
to the genuine metric j-threshold equivalence. -/
theorem metricJumpClassTag_eq_iff_close
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j) (x y : V) :
    metricJumpClassTag hpos hS hd j hj x =
      metricJumpClassTag hpos hS hd j hj y ↔
        d x y ≤ j := by
  constructor
  · intro h
    exact metricJumpClassLast_close_of_eq hpos hS hd j hj x y
      (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact metricJumpClassLast_eq_of_close hpos hS hd j hj x y h

/-- Class labels are monotone along the original j-convex order.
This is exactly the hypothesis required for lexicographic
refinement while preserving old side orders. -/
theorem metricJumpClassTag_mono
    {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (hconv : JumpConvex S d)
    (j : ℝ) (hj : Jump S j) :
    Monotone (metricJumpClassTag hpos hS hd j hj) := by
  intro x y hxy
  exact metricJumpClassLast_mono hpos hS hd hconv j hj hxy

end AllThoseRamseyClasses.Applications.MetricSaturation
