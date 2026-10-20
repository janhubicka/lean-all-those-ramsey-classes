import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Root-class cuts for compatible ordered metric jump partitions

The naive vertex root-cut order does NOT necessarily preserve
S-metric jump convexity. The correct one-jump construction
first orders whole j-equivalence classes, using the finite list
of root j-CLASSES as common landmarks.

These generic lemmas count how many fixed root-class labels
precede a given side-class label. They work with any finite
landmark index set, allowing later specialization to the
last-member representatives of the actual root j-classes.

The cut is monotone in the side-class label, is constant on
equal labels, strictly increases after a root label, and
agrees at corresponding root labels whenever their relative
orders agree on both sides. The latter is precisely the
compatibility needed before adding separate private-side
priorities and refining the vertex order.

No statement in this module assumes or proves that actual
metric class labels have already been amalgamated.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w z

/-- Count the root CLASS labels strictly below the class label
of a side vertex. The root index type need not be the original
set of root vertices: it will be the finite set of root classes. -/
noncomputable def rootClassCut
    {A : Type u} {X : Type v} {K : Type w}
    [Fintype A] [LinearOrder K]
    (rootClass : A → K) (label : X → K) (x : X) : ℕ :=
  ((Finset.univ : Finset A).filter
    (fun a => rootClass a < label x)).card

/-- A class-label map which does not decrease along the old order
induces a monotone cut in the common root-class list. -/
theorem rootClassCut_mono
    {A : Type u} {X : Type v} {K : Type w}
    [Fintype A] [LinearOrder K]
    (rootClass : A → K) (label : X → K)
    {x y : X} (hxy : label x ≤ label y) :
    rootClassCut rootClass label x ≤
      rootClassCut rootClass label y := by
  unfold rootClassCut
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact lt_of_lt_of_le ha hxy

/-- A cut depends only on the j-class label, never on which
representative vertex was chosen inside that class. -/
theorem rootClassCut_eq_of_label_eq
    {A : Type u} {X : Type v} {K : Type w}
    [Fintype A] [LinearOrder K]
    (rootClass : A → K) (label : X → K)
    {x y : X} (hxy : label x = label y) :
    rootClassCut rootClass label x =
      rootClassCut rootClass label y := by
  simp only [rootClassCut, hxy]

/-- A root class is not counted among the classes preceding
itself, but it is counted at every strictly later class. -/
theorem rootClassCut_strict_after_root
    {A : Type u} {X : Type v} {K : Type w}
    [Fintype A] [LinearOrder K]
    (rootClass : A → K) (label : X → K)
    (a : A) (x : X)
    (hax : rootClass a < label x) :
    rootClassCut rootClass id (rootClass a) <
      rootClassCut rootClass label x := by
  unfold rootClassCut
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨a, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl _
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb ⊢
    rcases hb with rfl | hba
    · exact hax
    · exact lt_trans hba hax

/-- The cuts computed on two DIFFERENT sides agree on the
corresponding shared root class, provided the root class
orders agree. No equality of the side class labels is needed. -/
theorem rootClassCut_root_agree
    {A : Type u} {K : Type v} {L : Type w}
    [Fintype A] [LinearOrder K] [LinearOrder L]
    (rootLeft : A → K) (rootRight : A → L)
    (hOrder : ∀ a b : A,
      rootLeft a < rootLeft b ↔ rootRight a < rootRight b)
    (a : A) :
    rootClassCut rootLeft id (rootLeft a) =
      rootClassCut rootRight id (rootRight a) := by
  unfold rootClassCut
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hOrder b a

end AllThoseRamseyClasses.Applications.MetricConvexOrder
