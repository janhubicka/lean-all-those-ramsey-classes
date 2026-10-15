import AllThoseRamseyClasses.Applications.MetricCanonicalFiniteLift

/-!
# An explicit metric on the canonical finite metric closure carrier

The preceding construction proves the existence of an S-metric
on the correct duplicate-free carrier consisting of old vertices
and canonical pairs (positive jump, quotient class). Here we
define the actual distance directly, using the representative
chosen by Quotient.out for each class.

Old-old distances remain d, each new-old distance is the
neutral-zero rounded sum j ⊕ d(root,x), distinct new tags get
the double sandwich j ⊕ d(root,root') ⊕ k, and the diagonal is zero.

This removes any arbitrary stage enumeration from the public
definition of the metric. The proof that this explicit operation
is a genuine S-metric reuses the certified existence theorem and
identifies all four kinds of distances with those of its witness.

The quotient-label characterization and root-choice invariance
can be established independently of the enumeration. The total
order and extension of embeddings remain separate obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The explicit canonical distance on the original vertices and
one closure vertex for every proper-jump equivalence class. -/
noncomputable def canonicalDistance {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    (V ⊕ CanonicalJumpTag hpos hS hd) →
      (V ⊕ CanonicalJumpTag hpos hS hd) → ℝ :=
  fun a b => by
    classical
    exact match a, b with
      | .inl x, .inl y => d x y
      | .inr tag, .inl x =>
          sumWithZero S (canonicalTagLevel tag) (d (canonicalTagRoot tag) x)
      | .inl x, .inr tag =>
          sumWithZero S (canonicalTagLevel tag) (d (canonicalTagRoot tag) x)
      | .inr a, .inr b =>
          if a = b then 0 else
            sumWithZero S
              (sumWithZero S (canonicalTagLevel a)
                (d (canonicalTagRoot a) (canonicalTagRoot b)))
              (canonicalTagLevel b)

@[simp] theorem canonicalDistance_old {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (x y : V) :
    canonicalDistance hpos hS hd (.inl x) (.inl y) = d x y := by
  rfl

@[simp] theorem canonicalDistance_new_old {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) (x : V) :
    canonicalDistance hpos hS hd (.inr tag) (.inl x) =
      sumWithZero S (canonicalTagLevel tag)
        (d (canonicalTagRoot tag) x) := by
  rfl

@[simp] theorem canonicalDistance_old_new {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) (x : V) :
    canonicalDistance hpos hS hd (.inl x) (.inr tag) =
      sumWithZero S (canonicalTagLevel tag)
        (d (canonicalTagRoot tag) x) := by
  rfl

@[simp] theorem canonicalDistance_new_diag {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) :
    canonicalDistance hpos hS hd (.inr tag) (.inr tag) = 0 := by
  simp [canonicalDistance]

theorem canonicalDistance_new_new {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd) (hab : a ≠ b) :
    canonicalDistance hpos hS hd (.inr a) (.inr b) =
      sumWithZero S
        (sumWithZero S (canonicalTagLevel a)
          (d (canonicalTagRoot a) (canonicalTagRoot b)))
        (canonicalTagLevel b) := by
  simp [canonicalDistance, hab]

/-- The formula-defined canonical lift is itself a genuine S-metric,
for every finite original metric including the empty vertex type.
For a nonempty base the checked existence theorem supplies a
witness with precisely the same four distance formulas. When the
base has no vertices, it has no jump quotient classes either,
so every metric axiom on the empty canonical carrier is vacuous. -/
theorem canonicalDistance_metric {S : Set ℝ} {V : Type u}
    [Finite V] (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    MetricOn S (canonicalDistance hpos hS hd) := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨D, hmetric, hOld, hNew, hCross⟩ :=
      exists_canonicalFiniteMetric_nonempty hV hfin hpos hS hassoc hd
    have hEq : ∀ a b : V ⊕ CanonicalJumpTag hpos hS hd,
        canonicalDistance hpos hS hd a b = D a b := by
      intro a b
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              exact (hOld x y).symm
          | inr tag =>
              calc
                canonicalDistance hpos hS hd (.inl x) (.inr tag) =
                    D (.inr tag) (.inl x) := by
                  rw [canonicalDistance_old_new, hNew]
                _ = D (.inl x) (.inr tag) :=
                  hmetric.symm _ _
      | inr tag =>
          cases b with
          | inl x =>
              exact (hNew tag x).symm
          | inr tag' =>
              by_cases heq : tag = tag'
              · subst tag'
                rw [canonicalDistance_new_diag]
                exact (hmetric.diag (.inr tag)).symm
              · rw [canonicalDistance_new_new hpos hS hd tag tag' heq]
                exact (hCross tag tag' heq).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      rw [hEq a a]
      exact hmetric.diag a
    · intro a b hab
      rw [hEq a b]
      exact hmetric.values a b hab
    · intro a b
      rw [hEq a b, hEq b a]
      exact hmetric.symm a b
    · intro a b c
      rw [hEq a c, hEq a b, hEq b c]
      exact hmetric.triangle a b c
  · have hnoV : ∀ x : V, False := by
      intro x
      exact hV ⟨x⟩
    have hnoTag : ∀ t : CanonicalJumpTag hpos hS hd, False := by
      intro t
      exact hnoV (canonicalTagRoot t)
    have hno : ∀ a : V ⊕ CanonicalJumpTag hpos hS hd, False := by
      intro a
      cases a with
      | inl x => exact hnoV x
      | inr t => exact hnoTag t
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      exact False.elim (hno a)
    · intro a b hab
      exact False.elim (hno a)
    · intro a b
      exact False.elim (hno a)
    · intro a b c
      exact False.elim (hno a)

end AllThoseRamseyClasses.Applications.MetricSaturation
