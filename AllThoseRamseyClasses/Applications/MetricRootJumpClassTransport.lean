import AllThoseRamseyClasses.Applications.MetricJumpClassLastMonotone

/-!
# Exact transport of ordered root jump-classes into finite metric sides

The class-cut construction for a convex S-metric amalgam needs the
SAME ordered list of *root jump-classes* on both original sides.
The existing canonical label of a finite jump-class is its last
original member; this file verifies how those labels are ordered
under a genuine isometric, strictly order-preserving embedding
of the common root into either side.

For distinct root j-classes, the last representatives of their
images in a convex side occur in EXACTLY the same relative
order as the root classes themselves, even if their last
members have moved outside the image of the root. In particular
the ordered root-class landmarks in the two metric sides agree.

This does not yet amalgamate the private class lists or provide
a convex order of the whole rooted metric pushout, and does not
assert anything about the printed weak local-completion proof.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Isometric order embeddings preserve STRICT ordering of
different root jump classes when those classes are represented
by their last original members. -/
theorem metricRootJumpClassImage_strictMono
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {U : Type v}
    [Finite A] [LinearOrder A] [Finite U] [LinearOrder U]
    {dA : A → A → ℝ} {dU : U → U → ℝ}
    (hdA : MetricOn S dA) (hdU : MetricOn S dU)
    (hconvU : JumpConvex S dU)
    (i : A → U)
    (hiOrder : StrictMono i)
    (hiDist : ∀ a b : A, dU (i a) (i b) = dA a b)
    (j : ℝ) (hj : Jump S j) :
    StrictMono
      (fun a : MetricJumpClassRep hpos hdA j hj =>
        metricJumpClassLast hpos hdU j hj (i a.val)) := by
  intro a b hab
  have habVal : a.val < b.val := hab
  have habSide : i a.val < i b.val := hiOrder habVal
  have hle :
      metricJumpClassLast hpos hdU j hj (i a.val) ≤
        metricJumpClassLast hpos hdU j hj (i b.val) :=
    metricJumpClassLast_mono hpos hS hdU hconvU j hj
      (le_of_lt habSide)
  have hne :
      metricJumpClassLast hpos hdU j hj (i a.val) ≠
        metricJumpClassLast hpos hdU j hj (i b.val) := by
    intro heq
    have hSideClose : dU (i a.val) (i b.val) ≤ j :=
      metricJumpClassLast_close_of_eq hpos hS hdU j hj
        (i a.val) (i b.val) heq
    have hRootClose : dA a.val b.val ≤ j := by
      rw [← hiDist a.val b.val]
      exact hSideClose
    have hRootLabel :
        metricJumpClassLast hpos hdA j hj a.val =
          metricJumpClassLast hpos hdA j hj b.val :=
      metricJumpClassLast_eq_of_close
        hpos hS hdA j hj a.val b.val hRootClose
    have heqVal : a.val = b.val := by
      calc
        a.val = metricJumpClassLast hpos hdA j hj a.val :=
          a.property.symm
        _ = metricJumpClassLast hpos hdA j hj b.val := hRootLabel
        _ = b.val := b.property
    exact (ne_of_lt hab) (Subtype.ext heqVal)
  exact lt_of_le_of_ne hle hne

/-- An injective strict monotone map of linear orders reflects
strict comparisons as well as preserving them. -/
private theorem strictMono_order_reflection
    {X : Type u} {Y : Type v}
    [LinearOrder X] [LinearOrder Y]
    {f : X → Y} (hf : StrictMono f)
    (x y : X) :
    f x < f y ↔ x < y := by
  constructor
  · intro h
    by_contra hn
    have hyx : y ≤ x := le_of_not_gt hn
    have hle : f y ≤ f x := hf.monotone hyx
    exact (not_lt_of_ge hle) h
  · intro hxy
    exact hf hxy

/-- The classes of one common isometric ordered root have the
SAME relative order when measured by the last-member label
of their images on either side. No equality of the selected
last vertices across the two different carriers is assumed. -/
theorem metricRootJumpClassImages_agree_order
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [LinearOrder A]
    [Finite U] [LinearOrder U]
    [Finite V] [LinearOrder V]
    {dA : A → A → ℝ}
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdA : MetricOn S dA)
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hconvU : JumpConvex S dU)
    (hconvV : JumpConvex S dV)
    (iU : A → U) (iV : A → V)
    (hiUOrder : StrictMono iU) (hiVOrder : StrictMono iV)
    (hiUDist : ∀ a b : A, dU (iU a) (iU b) = dA a b)
    (hiVDist : ∀ a b : A, dV (iV a) (iV b) = dA a b)
    (j : ℝ) (hj : Jump S j)
    (a b : MetricJumpClassRep hpos hdA j hj) :
    (metricJumpClassLast hpos hdU j hj (iU a.val) <
      metricJumpClassLast hpos hdU j hj (iU b.val)) ↔
    (metricJumpClassLast hpos hdV j hj (iV a.val) <
      metricJumpClassLast hpos hdV j hj (iV b.val)) := by
  let hLeft := metricRootJumpClassImage_strictMono
    hpos hS hdA hdU hconvU iU hiUOrder hiUDist j hj
  let hRight := metricRootJumpClassImage_strictMono
    hpos hS hdA hdV hconvV iV hiVOrder hiVDist j hj
  exact (strictMono_order_reflection hLeft a b).trans
    (strictMono_order_reflection hRight a b).symm

end AllThoseRamseyClasses.Applications.MetricSaturation
