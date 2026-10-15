import AllThoseRamseyClasses.Applications.MetricCanonicalJumpTags

/-!
# A metric on the paper's canonical closure-class vertices

For finite S and finite nonempty original V, the canonical closure
tags are exactly the pairs (positive jump j, original j-class).
The preceding finiteness theorem gives a bijection with
Fin n, with no duplicate tags. Use this bijection to pull the
checked tagged metric on V ⊕ Fin n back to the canonical carrier

    V ⊕ CanonicalJumpTag.

The metric has the paper's exact original-original,
original-closure and distinct closure-closure distance formulas.
The equality of a closure tag with itself gets distance zero,
not an inappropriate positive sandwich value.

This file is a metric existence result on the correct canonical
vertex type, not yet the order and embedding extension of the
complete 2019 lift. The empty V case is kept separate rather than
inventing an arbitrary default original root.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Restrict a genuine S-metric along an injective map. This
general-purpose lemma handles metric separation explicitly,
rather than silently relying on pseudometric pullback. -/
theorem metricOn_comap {S : Set ℝ} {V : Type u} {W : Type v}
    {d : W → W → ℝ} (hd : MetricOn S d)
    (f : V → W) (hf : Function.Injective f) :
    MetricOn S (fun x y : V => d (f x) (f y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact hd.diag (f x)
  · intro x y hxy
    apply hd.values (f x) (f y)
    intro h
    exact hxy (hf h)
  · intro x y
    exact hd.symm (f x) (f y)
  · intro x y z
    exact hd.triangle (f x) (f y) (f z)

/-- Reindex the finite tagged carrier using any bijection from
Fin n to the canonical tag type. -/
def canonicalTagIndexEquiv {V : Type u} {Tag : Type v} {n : ℕ}
    (e : Fin n ≃ Tag) : (V ⊕ Tag) ≃ (V ⊕ Fin n) where
  toFun
    | .inl x => .inl x
    | .inr t => .inr (e.symm t)
  invFun
    | .inl x => .inl x
    | .inr i => .inr (e i)
  left_inv := by
    intro x
    cases x with
    | inl x => rfl
    | inr x => simp
  right_inv := by
    intro x
    cases x with
    | inl x => rfl
    | inr x => simp

/-- A canonical finite closure lift exists for any nonempty finite
S-metric: the carrier has exactly one new vertex per genuine
positive-jump equivalence class, not per arbitrary attachment.

The three displayed distance laws completely determine its metric.
-/
theorem exists_canonicalFiniteMetric_nonempty {S : Set ℝ} {V : Type u}
    [Finite V] (hV : Nonempty V)
    (hfin : S.Finite) (hpos : Positive S)
    (hS : WellDefined S) (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    ∃ D : (V ⊕ CanonicalJumpTag hpos hS hd) →
        (V ⊕ CanonicalJumpTag hpos hS hd) → ℝ,
      MetricOn S D ∧
      (∀ x y : V, D (.inl x) (.inl y) = d x y) ∧
      (∀ (tag : CanonicalJumpTag hpos hS hd) (x : V),
        D (.inr tag) (.inl x) =
          sumWithZero S (canonicalTagLevel tag)
            (d (canonicalTagRoot tag) x)) ∧
      (∀ (a b : CanonicalJumpTag hpos hS hd), a ≠ b →
        D (.inr a) (.inr b) =
          sumWithZero S
            (sumWithZero S (canonicalTagLevel a)
              (d (canonicalTagRoot a) (canonicalTagRoot b)))
            (canonicalTagLevel b)) := by
  classical
  letI : Inhabited V := ⟨Classical.choice hV⟩
  obtain ⟨n, ⟨e⟩⟩ :=
    exists_canonicalTagEnumeration hfin hpos hS hd
  let roots : ℕ → V := fun i =>
    if h : i < n then canonicalTagRoot (e ⟨i, h⟩) else default
  let levels : ℕ → ℝ := fun i =>
    if h : i < n then canonicalTagLevel (e ⟨i, h⟩) else 0
  have hjumps : ∀ i, i < n → Jump S (levels i) := by
    intro i hi
    simp only [levels, dif_pos hi]
    exact canonicalTagLevel_jump (e ⟨i, hi⟩)
  let f : (V ⊕ CanonicalJumpTag hpos hS hd) ≃
      (V ⊕ Fin n) := canonicalTagIndexEquiv e
  let D : (V ⊕ CanonicalJumpTag hpos hS hd) →
      (V ⊕ CanonicalJumpTag hpos hS hd) → ℝ :=
    fun a b => taggedClosureDistance S d roots levels n (f a) (f b)
  have hm : MetricOn S (taggedClosureDistance S d roots levels n) :=
    taggedClosureDistance_metric hpos hS hassoc hd roots levels n hjumps
  have hmetric : MetricOn S D := metricOn_comap hm f f.injective
  have hroot : ∀ (t : CanonicalJumpTag hpos hS hd),
      roots (e.symm t).val = canonicalTagRoot t := by
    intro t
    simp only [roots, dif_pos (e.symm t).isLt]
    rw [show (⟨(e.symm t).val, (e.symm t).isLt⟩ : Fin n) =
      e.symm t by rfl, e.apply_symm_apply]
  have hlevel : ∀ (t : CanonicalJumpTag hpos hS hd),
      levels (e.symm t).val = canonicalTagLevel t := by
    intro t
    simp only [levels, dif_pos (e.symm t).isLt]
    rw [show (⟨(e.symm t).val, (e.symm t).isLt⟩ : Fin n) =
      e.symm t by rfl, e.apply_symm_apply]
  refine ⟨D, hmetric, ?_, ?_, ?_⟩
  · intro x y
    change taggedClosureDistance S d roots levels n (.inl x) (.inl y) =
      d x y
    exact taggedClosureDistance_old S d roots levels n x y
  · intro tag x
    change taggedClosureDistance S d roots levels n
      (.inr (e.symm tag)) (.inl x) =
        sumWithZero S (canonicalTagLevel tag)
          (d (canonicalTagRoot tag) x)
    rw [taggedClosureDistance_new_original, hlevel, hroot]
  · intro a b hab
    have hne : e.symm a ≠ e.symm b := by
      intro heq
      exact hab (e.symm.injective heq)
    change taggedClosureDistance S d roots levels n
      (.inr (e.symm a)) (.inr (e.symm b)) =
        sumWithZero S
          (sumWithZero S (canonicalTagLevel a)
            (d (canonicalTagRoot a) (canonicalTagRoot b)))
          (canonicalTagLevel b)
    rw [taggedClosureDistance_new_new hpos hS hassoc hd
      roots levels n hjumps (e.symm a) (e.symm b) hne,
      hlevel, hlevel, hroot, hroot]

end AllThoseRamseyClasses.Applications.MetricSaturation
