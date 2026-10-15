import AllThoseRamseyClasses.Applications.MetricCanonicalLiftEmbedding
import AllThoseRamseyClasses.Applications.MetricCanonicalClosureFunctions

/-!
# Uniqueness of the canonical closure lift of an isometry

Every canonical positive-jump closure tag is the value of the
corresponding closure function on an original vertex: choose an
original root in its quotient class. Consequently a map on the
lifted carrier extending the original isometry and preserving
these closure functions has no freedom on closure vertices.

The formal uniqueness theorem concerns *all* maps, not merely
isometric maps: the metric distance and order hypotheses are
irrelevant once the original action and the closure-function
commutation law have been fixed. The already verified metric
isometry theorem provides existence, so this discharges the
uniqueness portion of the metric-and-closure lift. The
paper's prescribed convex order remains separate.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Each canonical closure tag arises as the jump-closure function
value of its own chosen original class representative. -/
theorem canonicalClosureTag_of_root {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) :
    canonicalClosureTag hpos hS hd tag.1 (canonicalTagRoot tag) = tag := by
  apply Sigma.ext rfl
  exact canonicalTagRoot_class tag

/-- The induced canonical lift acts on a closure-function value
exactly as prescribed: take the jump class of the isometric image
of the original vertex. -/
theorem mapCanonicalLift_closure {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (j : PositiveJumpLevel S) (x : V) :
    mapCanonicalLift hpos hS hdV hdW f hf
        (.inr (canonicalClosureTag hpos hS hdV j x)) =
      .inr (canonicalClosureTag hpos hS hdW j (f x)) := by
  rfl

/-- **Uniqueness of the lifted embedding's underlying vertex map.**
Any map on original and canonical closure vertices that extends
the original f and commutes with all positive jump closure
functions is necessarily the canonical lift map.
No order assumption, injectivity axiom, or arbitrary choice
of additional closure vertices is needed. -/
theorem mapCanonicalLift_unique {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (g : (V ⊕ CanonicalJumpTag hpos hS hdV) →
      (W ⊕ CanonicalJumpTag hpos hS hdW))
    (hOld : ∀ x : V, g (.inl x) = .inl (f x))
    (hClosure : ∀ (j : PositiveJumpLevel S) (x : V),
      g (.inr (canonicalClosureTag hpos hS hdV j x)) =
        .inr (canonicalClosureTag hpos hS hdW j (f x))) :
    g = mapCanonicalLift hpos hS hdV hdW f hf := by
  funext a
  cases a with
  | inl x =>
      simpa only [mapCanonicalLift_old] using hOld x
  | inr tag =>
      have htag := canonicalClosureTag_of_root hpos hS hdV tag
      have h := hClosure tag.1 (canonicalTagRoot tag)
      have hlift := mapCanonicalLift_closure hpos hS hdV hdW
        f hf tag.1 (canonicalTagRoot tag)
      rw [htag] at h hlift
      exact h.trans hlift.symm

end AllThoseRamseyClasses.Applications.MetricSaturation
