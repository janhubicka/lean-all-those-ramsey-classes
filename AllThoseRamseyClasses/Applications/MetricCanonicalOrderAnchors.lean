import AllThoseRamseyClasses.Applications.MetricCanonicalInsertionOrder

/-!
# Monotonicity of original anchors in the canonical insertion order

Every canonical closure vertex (j,E) is inserted after the last
original member of E. Let anchor(x)=x for originals and
anchor((j,E))=lastOriginal(E) for closure tags.

The checked lexicographic insertion order has a simple
monotonicity property: if vertices move right, their
original anchors cannot move left. Conversely, a strict
increase of anchors forces the corresponding lifted
vertices to increase, independently of jump levels.

These lemmas reduce interval convexity for enlarged
jump classes to interval convexity in the original
linearly ordered metric space, without any induction
over the number of jumps.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The last-original-vertex anchor used in the lexicographic
order of a canonical original or closure vertex. -/
noncomputable def canonicalInsertionAnchor {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    V ⊕ CanonicalJumpTag hpos hS hd → V
  | .inl x => x
  | .inr tag => canonicalClassLast hpos hS hd tag

/-- The first component of an insertion key is precisely the
corresponding original anchor. -/
theorem canonicalInsertionKey_fst {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (x : V ⊕ CanonicalJumpTag hpos hS hd) :
    (ofLex (canonicalInsertionKey hpos hS hd x)).1 =
      canonicalInsertionAnchor hpos hS hd x := by
  cases x <;> rfl

/-- Strictly increasing original anchors force strictly
increasing positions in the canonical lifted order. -/
theorem canonicalInsertion_lt_of_anchor_lt {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (x y : V ⊕ CanonicalJumpTag hpos hS hd)
    (h : canonicalInsertionAnchor hpos hS hd x <
      canonicalInsertionAnchor hpos hS hd y) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      x < y) := by
  let a := ofLex (canonicalInsertionKey hpos hS hd x)
  let b := ofLex (canonicalInsertionKey hpos hS hd y)
  have hfst : a.1 < b.1 := by
    change (ofLex (canonicalInsertionKey hpos hS hd x)).1 <
      (ofLex (canonicalInsertionKey hpos hS hd y)).1
    rw [canonicalInsertionKey_fst, canonicalInsertionKey_fst]
    exact h
  have hlex : toLex a < toLex b :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl hfst)
  change canonicalInsertionKey hpos hS hd x <
    canonicalInsertionKey hpos hS hd y
  exact hlex

/-- The last-original-vertex anchor is monotone in the
canonical lifted linear order. A future interval proof can
therefore pass to original anchors without comparing all
four kinds of ordered metric vertices individually. -/
theorem canonicalInsertionAnchor_mono {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (x y : V ⊕ CanonicalJumpTag hpos hS hd)
    (hxy : (letI := canonicalInsertionLinearOrder hpos hS hd;
      x ≤ y)) :
    canonicalInsertionAnchor hpos hS hd x ≤
      canonicalInsertionAnchor hpos hS hd y := by
  letI : LinearOrder (V ⊕ CanonicalJumpTag hpos hS hd) :=
    canonicalInsertionLinearOrder hpos hS hd
  change x ≤ y at hxy
  by_contra hn
  have hyx : canonicalInsertionAnchor hpos hS hd y <
      canonicalInsertionAnchor hpos hS hd x := lt_of_not_ge hn
  have hlt := canonicalInsertion_lt_of_anchor_lt
    hpos hS hd y x hyx
  exact (not_lt_of_ge hxy) hlt

end AllThoseRamseyClasses.Applications.MetricSaturation
