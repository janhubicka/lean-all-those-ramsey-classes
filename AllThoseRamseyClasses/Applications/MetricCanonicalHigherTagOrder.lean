import AllThoseRamseyClasses.Applications.MetricCanonicalClassLastInLift
import AllThoseRamseyClasses.Applications.MetricCanonicalClosureFunctions

/-!
# Higher jump representatives lie after every smaller class they contain

The paper orders the canonical metric lift lexicographically by the last
original vertex of a threshold class, then by increasing jump level.
This order prevents a high-level closure representative from appearing
inside a smaller-jump class it contains.

Suppose j<k and the root of a k-closure tag lies in the original
j-class of x. Then the last original vertex of the j-class of x
also lies in the k-class. So the last original anchor of the
j-closure is at most that of the k-closure; a strict inequality
decides their order, and equality is resolved by j<k.

The proof needs only the genuine S-metric and the jump identities.
Original block convexity is NOT an additional assumption. This
is a reusable separation lemma for proving that completed jump
classes are intervals in the canonical insertion order.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A larger-level canonical closure tag whose original root belongs
to the smaller j-class of x necessarily occurs *after* the j-closure
of x. This excludes any k>j closure vertex from occurring between
old members of the j-class and its designated last closure vertex. -/
theorem canonicalInsertion_higher_tag_after_class {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : PositiveJumpLevel S) (x : V)
    (other : CanonicalJumpTag hpos hS hd)
    (hlevel : j.val < canonicalTagLevel other)
    (hroot : d (canonicalTagRoot other) x ≤ j.val) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inr (canonicalClosureTag hpos hS hd j x) :
        V ⊕ CanonicalJumpTag hpos hS hd) < Sum.inr other) := by
  let c : CanonicalJumpTag hpos hS hd :=
    canonicalClosureTag hpos hS hd j x
  have hcroot : d (canonicalTagRoot c) x ≤ j.val :=
    canonicalClosureTag_root_threshold hpos hS hd j x
  have hclast : d (canonicalClassLast hpos hS hd c)
      (canonicalTagRoot c) ≤ j.val :=
    canonicalClassLast_mem hpos hS hd c
  have hlastx : d (canonicalClassLast hpos hS hd c) x ≤ j.val :=
    metric_jump_threshold_trans hpos hS hd (Or.inr j.property)
      (canonicalClassLast hpos hS hd c)
      (canonicalTagRoot c) x hclast hcroot
  have hxother : d x (canonicalTagRoot other) ≤ j.val := by
    rw [hd.symm x (canonicalTagRoot other)]
    exact hroot
  have hlastother : d (canonicalClassLast hpos hS hd c)
      (canonicalTagRoot other) ≤ j.val :=
    metric_jump_threshold_trans hpos hS hd (Or.inr j.property)
      (canonicalClassLast hpos hS hd c)
      x (canonicalTagRoot other) hlastx hxother
  have hanchor : canonicalClassLast hpos hS hd c ≤
      canonicalClassLast hpos hS hd other :=
    canonicalClassLast_max hpos hS hd other
      (canonicalClassLast hpos hS hd c)
      (hlastother.trans (le_of_lt hlevel))
  have hclevel : canonicalTagLevel c = j.val :=
    canonicalClosureTag_level hpos hS hd j x
  change (letI := canonicalInsertionLinearOrder hpos hS hd;
    (Sum.inr c : V ⊕ CanonicalJumpTag hpos hS hd) < Sum.inr other)
  rcases lt_or_eq_of_le hanchor with hlt | heq
  · exact canonicalInsertion_tag_lt_tag_of_last_lt
      hpos hS hd c other hlt
  · exact canonicalInsertion_increasing_levels hpos hS hd
      c other heq (by rw [hclevel]; exact hlevel)

end AllThoseRamseyClasses.Applications.MetricSaturation
