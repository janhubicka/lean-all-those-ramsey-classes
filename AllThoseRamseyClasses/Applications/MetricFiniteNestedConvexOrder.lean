import AllThoseRamseyClasses.Applications.MetricNestedConvexPreservation
import Mathlib.Tactic

/-!
# One common linear order for a finite nested hierarchy of class labels

The existing one-step lemma says that sorting by a coarser
class label preserves each already-convex finer class.
Here we iterate this step over an arbitrary finite list
of classes, written from FINEST to COARSEST.

The result is a single genuine linear order on exactly
the original vertices in which EVERY listed class fibre
is an interval. Moreover an original strict comparison
survives whenever all level keys are nondecreasing along
that comparison. Thus old side orders can be preserved
through a complete finite chain of metric jump levels.

All of this is generic finite order combinatorics.
Construction and compatibility of the actual class labels
on a rooted S-metric strong amalgam are separate obligations.
No auxiliary F_j or printed exact weak completion is inferred.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v

/-- Each finer class is contained in a single class at
EVERY later (coarser) level. This is the finite version
of a nested proper-jump metric equivalence hierarchy. -/
def NestedLevels {X : Type u} {K : Type v} :
    List (X → K) → Prop
  | [] => True
  | fine :: rest =>
      (∀ coarse ∈ rest, ∀ x y : X,
        fine x = fine y → coarse x = coarse y) ∧
      NestedLevels rest

/-- Apply class-first refinements in the order given by a
finite sequence of labels. When the sequence is ordered
from finest to coarsest, the final order is convex at
all levels by the theorem below. -/
noncomputable def refineClassLevels
    {X : Type u} {K : Type v} [LinearOrder K]
    (o : LinearOrder X)
    (levels : List (X → K)) : LinearOrder X :=
  levels.foldl
    (fun (current : LinearOrder X) (label : X → K) =>
      @labelFirstOrder X K current _ label) o

/-- A finite number of class refinements does not disturb
a comparison from the original order if each chosen
class label is nondecreasing on that pair. This is the
exact old-side order preservation invariant. -/
theorem refineClassLevels_preserves_comparison
    {X : Type u} {K : Type v} [LinearOrder K]
    (o : LinearOrder X) (levels : List (X → K))
    (x y : X)
    (hxy : @LT.lt X o.toLT x y)
    (hKeys : ∀ label ∈ levels, label x ≤ label y) :
    @LT.lt X (refineClassLevels o levels).toLT x y := by
  induction levels generalizing o with
  | nil =>
      change @LT.lt X o.toLT x y
      exact hxy
  | cons label rest ih =>
      let o' : LinearOrder X := @labelFirstOrder X K o _ label
      have hFirst : @LT.lt X o'.toLT x y :=
        @labelFirst_strict_of_label_mono X K o _ label x y hxy
          (hKeys label (by simp))
      have hLater : ∀ next ∈ rest, next x ≤ next y := by
        intro next hn
        exact hKeys next (by simp [hn])
      have hResult :=
        ih o' hFirst hLater
      change @LT.lt X (refineClassLevels o' rest).toLT x y
      exact hResult

/-- General finite induction invariant: all previously
convex fibres remain convex when the new coarser
levels are processed, and each newly processed
class fibre also becomes convex. -/
theorem refineClassLevels_preserves_prior_convex
    {X : Type u} {K : Type v} [LinearOrder K]
    (o : LinearOrder X)
    (done todo : List (X → K))
    (hDone : ∀ f ∈ done, FibreConvex o f)
    (hCross : ∀ f ∈ done, ∀ g ∈ todo,
      ∀ x y : X, f x = f y → g x = g y)
    (hNested : NestedLevels todo) :
    ∀ f ∈ done ++ todo,
      FibreConvex (refineClassLevels o todo) f := by
  induction todo generalizing o done with
  | nil =>
      intro f hf
      have hd : f ∈ done := by simpa using hf
      simpa [refineClassLevels] using hDone f hd
  | cons g rest ih =>
      have hTop : ∀ next ∈ rest, ∀ x y : X,
          g x = g y → next x = next y := hNested.1
      have hTail : NestedLevels rest := hNested.2
      let o' : LinearOrder X := @labelFirstOrder X K o _ g
      have hDone' : ∀ f ∈ g :: done, FibreConvex o' f := by
        intro f hf
        rcases List.mem_cons.mp hf with hEq | hfOld
        · subst f
          exact @labelFirst_coarse_fibre_convex X K o _ g
        · exact @labelFirst_preserves_nested_fibre_convex X K K o _
            g f (fun x y heq => hCross f hfOld g (by simp) x y heq)
            (hDone f hfOld)
      have hCross' : ∀ f ∈ g :: done, ∀ next ∈ rest,
          ∀ x y : X, f x = f y → next x = next y := by
        intro f hf next hnext x y heq
        rcases List.mem_cons.mp hf with hEq | hfOld
        · subst f
          exact hTop next hnext x y heq
        · exact hCross f hfOld next (by simp [hnext]) x y heq
      have hIH :=
        ih o' (g :: done) hDone' hCross' hTail
      intro f hf
      have hMem : f ∈ (g :: done) ++ rest := by
        simp only [List.mem_append, List.mem_cons] at hf ⊢
        tauto
      have hF := hIH f hMem
      change FibreConvex (refineClassLevels o' rest) f
      exact hF

/-- An ARBITRARY finite nested hierarchy of labels can be
made simultaneously convex by a SINGLE linear order.
No fixed upper bound on the number of levels is needed. -/
theorem refineClassLevels_all_convex
    {X : Type u} {K : Type v} [LinearOrder K]
    (o : LinearOrder X)
    (levels : List (X → K))
    (hNested : NestedLevels levels) :
    ∀ label ∈ levels,
      FibreConvex (refineClassLevels o levels) label := by
  have hDone : ∀ f ∈ ([] : List (X → K)), FibreConvex o f := by
    intro f hf
    cases hf
  have hCross : ∀ f ∈ ([] : List (X → K)),
      ∀ g ∈ levels, ∀ x y : X,
        f x = f y → g x = g y := by
    intro f hf
    cases hf
  have h :=
    refineClassLevels_preserves_prior_convex
      o [] levels hDone hCross hNested
  simpa using h

end AllThoseRamseyClasses.Applications.MetricConvexOrder
