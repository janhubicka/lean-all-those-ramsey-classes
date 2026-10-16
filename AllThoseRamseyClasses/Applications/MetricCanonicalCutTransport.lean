import AllThoseRamseyClasses.Applications.MetricCanonicalClassLast
import AllThoseRamseyClasses.Applications.MetricCanonicalQuotientMap
import AllThoseRamseyClasses.Applications.MetricConvexityTransfer

/-!
# Invariance of original class insertion cuts under ordered isometries

A canonical closure vertex is placed just after the last ORIGINAL
vertex of its jump-equivalence class. An embedding of the original
metric need not map the last member of a small class to the last
member of the corresponding larger target class, because the
larger target may contain additional original vertices.

The correct invariant is the *cut induced on the original image*:
for an exact order-preserving isometry f:V→W and each source
canonical jump tag t,

  x ≤ lastOriginal_V(t)  ↔
  f(x) ≤ lastOriginal_W(mapCanonicalJumpTag f t).

This follows from convexity in the target order: source and
target classes intersect the embedded copy in precisely the
same original vertices, so the additional target vertices
cannot move a class's last member across an original image
vertex outside that class.

This is a reusable order-embedding lemma. It does not yet
compare pairs of new canonical closure tags; that will require
nested/disjoint jump-class comparisons.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- The canonical class-last insertion cut agrees on every
original source vertex with the cut of the image jump class
in a convexly ordered target S-metric.

No finiteness of S is used, only finite original vertex sets
(for the two maxima), exact distance reflection, a strict
original order embedding and jump-convexity of the target.
-/
theorem canonicalClassLast_cut_iff_under_isometry {S : Set ℝ}
    {V : Type u} {W : Type v}
    [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (hconvW : JumpConvex S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (hstrict : StrictMono f)
    (tag : CanonicalJumpTag hpos hS hdV) (x : V) :
    x ≤ canonicalClassLast hpos hS hdV tag ↔
      f x ≤ canonicalClassLast hpos hS hdW
        (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) := by
  let srcLast := canonicalClassLast hpos hS hdV tag
  let tgtTag := mapCanonicalJumpTag hpos hS hdV hdW f hf tag
  let tgtLast := canonicalClassLast hpos hS hdW tgtTag
  have hSrcClass :
      Quotient.mk
        (jumpSetoid hpos hS hdV tag.1.val
          (Or.inr tag.1.property)) srcLast = tag.2 :=
    canonicalClassLast_class hpos hS hdV tag
  have hImageClass :
      Quotient.mk
        (jumpSetoid hpos hS hdW tag.1.val
          (Or.inr tag.1.property)) (f srcLast) = tgtTag.2 :=
    mapCanonicalJumpTag_class_mk hpos hS hdV hdW f hf
      tag srcLast hSrcClass
  have hTargetRoot :
      Quotient.mk
        (jumpSetoid hpos hS hdW tag.1.val
          (Or.inr tag.1.property)) (canonicalTagRoot tgtTag) =
        tgtTag.2 :=
    canonicalTagRoot_class tgtTag
  have hLevel : canonicalTagLevel tgtTag = canonicalTagLevel tag := by
    change canonicalTagLevel
      (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) = canonicalTagLevel tag
    exact mapCanonicalJumpTag_level hpos hS hdV hdW f hf tag
  have hImageRoot : dW (f srcLast) (canonicalTagRoot tgtTag) ≤
      canonicalTagLevel tag :=
    Quotient.exact (hImageClass.trans hTargetRoot.symm)
  have hImageRoot' : dW (f srcLast)
      (canonicalTagRoot tgtTag) ≤ canonicalTagLevel tgtTag := by
    rw [hLevel]
    exact hImageRoot
  have hLastImage : f srcLast ≤ tgtLast :=
    canonicalClassLast_max hpos hS hdW tgtTag (f srcLast)
      hImageRoot'
  constructor
  · intro hx
    exact (hstrict.monotone hx).trans hLastImage
  · intro hx
    by_contra hnot
    have hslt : srcLast < x := lt_of_not_ge hnot
    have hFlt : f srcLast < f x := hstrict hslt
    have hTargetMem : dW tgtLast (canonicalTagRoot tgtTag) ≤
        canonicalTagLevel tgtTag :=
      canonicalClassLast_mem hpos hS hdW tgtTag
    have hRootLast : dW (canonicalTagRoot tgtTag) tgtLast ≤
        canonicalTagLevel tag := by
      rw [hdW.symm (canonicalTagRoot tgtTag) tgtLast]
      simpa only [hLevel] using hTargetMem
    have hEnds : dW (f srcLast) tgtLast ≤
        canonicalTagLevel tag :=
      metric_jump_threshold_trans hpos hS hdW
        (Or.inr (canonicalTagLevel_jump tag))
        (f srcLast) (canonicalTagRoot tgtTag) tgtLast
        hImageRoot hRootLast
    have hFxClose : dW (f srcLast) (f x) ≤
        canonicalTagLevel tag :=
      (hconvW (canonicalTagLevel tag)
        (canonicalTagLevel_jump tag)
        (f srcLast) (f x) tgtLast
        (le_of_lt hFlt) hx hEnds).1
    have hSrcClose : dV x srcLast ≤ canonicalTagLevel tag := by
      rw [hdV.symm x srcLast, ← hf srcLast x]
      exact hFxClose
    have hSrcLastMem : dV srcLast (canonicalTagRoot tag) ≤
        canonicalTagLevel tag :=
      canonicalClassLast_mem hpos hS hdV tag
    have hxRoot : dV x (canonicalTagRoot tag) ≤
        canonicalTagLevel tag :=
      metric_jump_threshold_trans hpos hS hdV
        (Or.inr (canonicalTagLevel_jump tag))
        x srcLast (canonicalTagRoot tag)
        hSrcClose hSrcLastMem
    have hle := canonicalClassLast_max hpos hS hdV tag x hxRoot
    exact (not_lt_of_ge hle) hslt

end AllThoseRamseyClasses.Applications.MetricSaturation
