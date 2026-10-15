import AllThoseRamseyClasses.Applications.MetricCanonicalDistance

/-!
# Transport of jump-equivalence classes along isometric embeddings

The equivalence relation d(x,y) <= j is defined for every proper
jump j, and also for the zero threshold. An exact isometric map
of original S-metric spaces preserves and reflects the relation.

This module constructs the induced map on the quotient classes
using Quotient.liftOn, proves its computation on representatives
and proves injectivity (reflection is essential here). It then
defines the induced map of the canonical (positive jump,class)
closure tags, preserving their jump levels.

The actual metric-isometry extension to the enlarged canonical
carriers is a separate step: its proof also needs the established
representative-independence of the rounded cross-labels.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- An isometry of the original metric maps threshold equivalence
classes at the same jump level to threshold equivalence classes. -/
noncomputable def mapJumpClass {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) :
    JumpClasses hpos hS hdV j hj →
      JumpClasses hpos hS hdW j hj :=
  fun q =>
    Quotient.liftOn q
      (fun x => Quotient.mk (jumpSetoid hpos hS hdW j hj) (f x))
      (by
        intro a b hab
        apply Quotient.sound
        change dW (f a) (f b) ≤ j
        rw [hf a b]
        exact hab)

/-- The quotient map computes by applying the original isometry
to any chosen representative of the class. -/
@[simp] theorem mapJumpClass_mk {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) (x : V) :
    mapJumpClass hpos hS hdV hdW f hf j hj
        (Quotient.mk (jumpSetoid hpos hS hdV j hj) x) =
      Quotient.mk (jumpSetoid hpos hS hdW j hj) (f x) := by
  rfl

/-- The induced quotient map is injective: if images are in the
same jump class, the exact isometry reflects that relation. -/
theorem mapJumpClass_injective {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) :
    Function.Injective (mapJumpClass hpos hS hdV hdW f hf j hj) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          apply Quotient.sound
          have hW : Quotient.mk (jumpSetoid hpos hS hdW j hj) (f x) =
              Quotient.mk (jumpSetoid hpos hS hdW j hj) (f y) := hqr
          have hle : dW (f x) (f y) ≤ j := Quotient.exact hW
          change dV x y ≤ j
          rw [← hf x y]
          exact hle

/-- The induced map on canonical closure tags preserves their
positive jump levels and takes a quotient class to its image
under the exact isometry. -/
noncomputable def mapCanonicalJumpTag {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y) :
    CanonicalJumpTag hpos hS hdV →
      CanonicalJumpTag hpos hS hdW :=
  fun tag => ⟨tag.1,
    mapJumpClass hpos hS hdV hdW f hf
      tag.1.val (Or.inr tag.1.property) tag.2⟩

@[simp] theorem mapCanonicalJumpTag_level {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (tag : CanonicalJumpTag hpos hS hdV) :
    canonicalTagLevel (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) =
      canonicalTagLevel tag := rfl

/-- Image of a canonical tag class represented by an original
vertex is the class represented by the isometric image vertex. -/
theorem mapCanonicalJumpTag_class_mk {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (tag : CanonicalJumpTag hpos hS hdV) (x : V)
    (hx : Quotient.mk
        (jumpSetoid hpos hS hdV tag.1.val
          (Or.inr tag.1.property)) x = tag.2) :
    Quotient.mk
        (jumpSetoid hpos hS hdW tag.1.val
          (Or.inr tag.1.property)) (f x) =
      (mapCanonicalJumpTag hpos hS hdV hdW f hf tag).2 := by
  change Quotient.mk
      (jumpSetoid hpos hS hdW tag.1.val
        (Or.inr tag.1.property)) (f x) =
    mapJumpClass hpos hS hdV hdW f hf tag.1.val
      (Or.inr tag.1.property) tag.2
  rw [← hx]
  exact (mapJumpClass_mk hpos hS hdV hdW f hf
    tag.1.val (Or.inr tag.1.property) x).symm

end AllThoseRamseyClasses.Applications.MetricSaturation
