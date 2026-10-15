import AllThoseRamseyClasses.Applications.MetricClosureTowerLabels

/-!
# A directly indexed finite metric closure lift

Instead of exposing an n-fold nested Option type to applications,
reindex the checked finite closure tower by the convenient carrier

    V ⊕ Fin n,

with original x at Sum.inl x and the i-th newly attached closure
vertex at Sum.inr i. The complete metric is pulled back from
the verified tower metric.

The off-diagonal separation proof is supplied explicitly, using
the pairwise rounded-sum formulas: it does NOT assume that the
stage-indexing map is injective or that an arbitrary pullback is
a metric. No quotient identifications are performed: selecting
one stage for each canonical (jump,class) is a separate step.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Represent every directly tagged vertex in the checked tower. -/
def taggedTowerVertex {V : Type u} (n : ℕ) :
    V ⊕ Fin n → ClosureTower V n
  | .inl x => towerOriginal n x
  | .inr i => towerClosure n i.val i.isLt

/-- The finite S-metric on a directly tagged carrier. It is built
from an already verified tower, not from unproved triangles. -/
noncomputable def taggedClosureDistance (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (roots : ℕ → V) (levels : ℕ → ℝ)
    (n : ℕ) (a b : V ⊕ Fin n) : ℝ :=
  closureTowerDistance S d roots levels n
    (taggedTowerVertex n a) (taggedTowerVertex n b)

/-- The old metric is literally preserved in the tagged carrier. -/
@[simp] theorem taggedClosureDistance_old (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (roots : ℕ → V) (levels : ℕ → ℝ)
    (n : ℕ) (x y : V) :
    taggedClosureDistance S d roots levels n (.inl x) (.inl y) =
      d x y := by
  exact closureTowerDistance_old S d roots levels n x y

/-- Every i-th tagged closure retains its original-root distance. -/
@[simp] theorem taggedClosureDistance_new_original (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (roots : ℕ → V) (levels : ℕ → ℝ)
    (n : ℕ) (i : Fin n) (x : V) :
    taggedClosureDistance S d roots levels n (.inr i) (.inl x) =
      sumWithZero S (levels i.val) (d (roots i.val) x) := by
  exact closureTowerDistance_closure_original S d roots levels n i.val i.isLt x

/-- Original-to-new distances follow from the metric symmetry,
with no additional operation on the distance set. -/
theorem taggedClosureDistance_original_new {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) (n : ℕ)
    (hlevels : ∀ i, i < n → Jump S (levels i))
    (x : V) (i : Fin n) :
    taggedClosureDistance S d roots levels n (.inl x) (.inr i) =
      sumWithZero S (levels i.val) (d (roots i.val) x) := by
  have hm := closureTowerDistance_metric hpos hS hassoc hd
    roots levels n hlevels
  calc
    taggedClosureDistance S d roots levels n (.inl x) (.inr i) =
        taggedClosureDistance S d roots levels n (.inr i) (.inl x) :=
      hm.symm _ _
    _ = sumWithZero S (levels i.val) (d (roots i.val) x) :=
      taggedClosureDistance_new_original S d roots levels n i x

/-- Distinct tags have the precisely computed quotient-sandwich
distance, independently of which other tags are present. -/
theorem taggedClosureDistance_new_new {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) (n : ℕ)
    (hlevels : ∀ i, i < n → Jump S (levels i))
    (i k : Fin n) (hik : i ≠ k) :
    taggedClosureDistance S d roots levels n (.inr i) (.inr k) =
      sumWithZero S
        (sumWithZero S (levels i.val)
          (d (roots i.val) (roots k.val))) (levels k.val) := by
  have hne : i.val ≠ k.val := by
    intro heq
    exact hik (Fin.ext heq)
  exact closureTowerDistance_twoClosures hpos hS hassoc hd
    roots levels n hlevels i.val k.val i.isLt k.isLt hne

/-- Finite tagged closure construction is a genuine S-metric,
not merely a pseudo-metric. Off-diagonal values belong to
the positive distance set S, even when roots coincide. -/
theorem taggedClosureDistance_metric {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) (n : ℕ)
    (hlevels : ∀ i, i < n → Jump S (levels i)) :
    MetricOn S (taggedClosureDistance S d roots levels n) := by
  have hm := closureTowerDistance_metric hpos hS hassoc hd
    roots levels n hlevels
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact hm.diag (taggedTowerVertex n a)
  · intro a b hab
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            rw [taggedClosureDistance_old]
            apply hd.values x y
            intro hxy
            exact hab (congrArg Sum.inl hxy)
        | inr k =>
            rw [taggedClosureDistance_original_new hpos hS hassoc
              hd roots levels n hlevels x k]
            exact sumWithZero_mem_of_left_mem hpos hS
              (hlevels k.val k.isLt).1
              (metric_value_mem hd (roots k.val) x)
    | inr i =>
        cases b with
        | inl y =>
            rw [taggedClosureDistance_new_original]
            exact sumWithZero_mem_of_left_mem hpos hS
              (hlevels i.val i.isLt).1
              (metric_value_mem hd (roots i.val) y)
        | inr k =>
            have hik : i ≠ k := by
              intro heq
              exact hab (congrArg Sum.inr heq)
            rw [taggedClosureDistance_new_new hpos hS hassoc hd
              roots levels n hlevels i k hik]
            have hfirst : sumWithZero S (levels i.val)
                (d (roots i.val) (roots k.val)) ∈ S :=
              sumWithZero_mem_of_left_mem hpos hS
                (hlevels i.val i.isLt).1
                (metric_value_mem hd (roots i.val) (roots k.val))
            exact sumWithZero_mem_of_left_mem hpos hS hfirst
              (Or.inr (hlevels k.val k.isLt).1)
  · intro a b
    exact hm.symm (taggedTowerVertex n a) (taggedTowerVertex n b)
  · intro a b c
    exact hm.triangle (taggedTowerVertex n a)
      (taggedTowerVertex n b) (taggedTowerVertex n c)

/-- For a finite original space, the tagged lift is visibly finite.
No recursive type needs to appear in a user's API. -/
theorem taggedClosure_finite {V : Type u} [Finite V] (n : ℕ) :
    Finite (V ⊕ Fin n) := by
  infer_instance

end AllThoseRamseyClasses.Applications.MetricSaturation
