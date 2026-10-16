import AllThoseRamseyClasses.Applications.MetricCanonicalHigherTagOrder
import AllThoseRamseyClasses.Applications.MetricCanonicalOrderAnchors
import AllThoseRamseyClasses.Applications.MetricConvexityTransfer
import AllThoseRamseyClasses.Applications.MetricBlockConvexity

/-!
# Convexity of canonical finite metric closure lifts

The canonical insertion order is obtained by sorting old vertices and
canonical (proper jump, original equivalence class) tags by the last
original member of their class, with a jump-level tie breaker.

Here we prove the full *jump-threshold* convexity of this order for the
actual metric on the canonical lift whenever the original finite
S-metric order is jump-convex. Together with the checked finite
paper-block/jump equivalence, this gives the paper's metric
block-convexity for the lift.

Proof idea, without induction on jumps:

* A jump-j-close pair of *distinct* lifted vertices has all its
  positive closure levels at most j.
* Replace both endpoints by their last-original anchors. The anchors
  remain j-close, since each attachment lies j-close to its anchor.
* The anchor map is monotone in the inserted linear order. Original
  jump-convexity therefore puts every intermediate anchor in the
  same original j-class.
* A closure vertex at higher level k>j cannot lie between these
  endpoints. The checked higher-tag lemma places it strictly after
  the j-closure of that original class, while the second endpoint
  lies at or before the j-closure by the checked last-class theorem.
* All remaining intermediate vertices are j-close via their
  original anchors and the metric-jump transitivity theorem.

This proves the entire jump-class convexity theorem. The subsequent
order-preservation of lifted embeddings and class-level Ramsey
conditions are separate tasks.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- An original vertex is always active at a jump threshold;
a canonical closure vertex is active at threshold j precisely
when its own positive attachment level is at most j. -/
def canonicalActiveAtJump {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) (j : ℝ) :
    V ⊕ CanonicalJumpTag hpos hS hd → Prop
  | .inl _ => True
  | .inr t => canonicalTagLevel t ≤ j

/-- At a jump threshold, both endpoints of a non-diagonal
j-close pair are active: positive closure levels exceeding j
form singleton j-equivalence classes. -/
theorem canonicalActive_of_close_ne {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j)
    (a b : V ⊕ CanonicalJumpTag hpos hS hd)
    (hne : a ≠ b)
    (hab : canonicalDistance hpos hS hd a b ≤ j) :
    canonicalActiveAtJump hpos hS hd j a ∧
      canonicalActiveAtJump hpos hS hd j b := by
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          exact ⟨trivial, trivial⟩
      | inr t =>
          have h' : canonicalDistance hpos hS hd
              (.inr t) (.inl x) ≤ j := by
            simpa only [canonicalDistance_old_new,
              canonicalDistance_new_old] using hab
          have ht := ((canonicalDistance_closure_old_le_jump_iff
            hpos hS hd t x hj).mp h').1
          exact ⟨trivial, ht⟩
  | inr t =>
      cases b with
      | inl y =>
          have ht := ((canonicalDistance_closure_old_le_jump_iff
            hpos hS hd t y hj).mp hab).1
          exact ⟨ht, trivial⟩
      | inr v =>
          have htv : t ≠ v := by
            intro h
            apply hne
            exact congrArg
              (fun t : CanonicalJumpTag hpos hS hd =>
                (Sum.inr t : V ⊕ CanonicalJumpTag hpos hS hd)) h
          have ht := (canonicalDistance_closure_closure_le_jump_iff
            hpos hS hd t v htv hj).mp hab
          exact ⟨ht.1, ht.2.2⟩

/-- An active lifted vertex is within jump distance j of
its original last-member anchor. This holds even if the
vertex is itself a closure-class representative. -/
theorem canonicalAnchor_close_active {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j)
    (a : V ⊕ CanonicalJumpTag hpos hS hd)
    (hactive : canonicalActiveAtJump hpos hS hd j a) :
    canonicalDistance hpos hS hd
      (.inl (canonicalInsertionAnchor hpos hS hd a)) a ≤ j := by
  cases a with
  | inl x =>
      change d x x ≤ j
      rw [hd.diag x]
      exact (hpos j hj.1).le
  | inr tag =>
      have hlevel : canonicalTagLevel tag ≤ j := hactive
      have hroot : d (canonicalTagRoot tag)
          (canonicalClassLast hpos hS hd tag) ≤ j := by
        rw [hd.symm (canonicalTagRoot tag)
          (canonicalClassLast hpos hS hd tag)]
        exact (canonicalClassLast_mem hpos hS hd tag).trans hlevel
      change canonicalDistance hpos hS hd
        (.inr tag) (.inl (canonicalClassLast hpos hS hd tag)) ≤ j
      exact (canonicalDistance_closure_old_le_jump_iff
        hpos hS hd tag (canonicalClassLast hpos hS hd tag) hj).mpr
          ⟨hlevel, hroot⟩

/-- If two active vertices are j-close in the canonical lift,
their last-original anchors are j-close in the original metric.
Only metric-jump transitivity is used, not convexity. -/
theorem canonicalAnchors_close_of_close {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    {j : ℝ} (hj : Jump S j)
    (hLift : MetricOn S (canonicalDistance hpos hS hd))
    (a b : V ⊕ CanonicalJumpTag hpos hS hd)
    (ha : canonicalActiveAtJump hpos hS hd j a)
    (hb : canonicalActiveAtJump hpos hS hd j b)
    (hab : canonicalDistance hpos hS hd a b ≤ j) :
    d (canonicalInsertionAnchor hpos hS hd a)
      (canonicalInsertionAnchor hpos hS hd b) ≤ j := by
  have hA := canonicalAnchor_close_active hpos hS hd hj a ha
  have hB := canonicalAnchor_close_active hpos hS hd hj b hb
  have hBrev : canonicalDistance hpos hS hd b
      (.inl (canonicalInsertionAnchor hpos hS hd b)) ≤ j := by
    calc
      canonicalDistance hpos hS hd b
          (.inl (canonicalInsertionAnchor hpos hS hd b)) =
        canonicalDistance hpos hS hd
          (.inl (canonicalInsertionAnchor hpos hS hd b)) b :=
        hLift.symm _ _
      _ ≤ j := hB
  have hAB := metric_jump_threshold_trans hpos hS hLift
    (Or.inr hj)
    (.inl (canonicalInsertionAnchor hpos hS hd a))
    a b hA hab
  have hAnchors := metric_jump_threshold_trans hpos hS hLift
    (Or.inr hj)
    (.inl (canonicalInsertionAnchor hpos hS hd a))
    b (.inl (canonicalInsertionAnchor hpos hS hd b))
    hAB hBrev
  simpa only [canonicalDistance_old] using hAnchors

/-- The canonical insertion order is convex at every proper jump
whenever the original S-metric order is so. This is the
full metric convexity of the canonical finite lift,
with NO extra ordering axiom and no jump-level induction. -/
theorem canonicalLift_jumpConvex {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (hconv : JumpConvex S d) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      JumpConvex S (canonicalDistance hpos hS hd)) := by
  letI : LinearOrder (V ⊕ CanonicalJumpTag hpos hS hd) :=
    canonicalInsertionLinearOrder hpos hS hd
  change JumpConvex S (canonicalDistance hpos hS hd)
  have hLift : MetricOn S (canonicalDistance hpos hS hd) :=
    canonicalDistance_metric hfin hpos hS hassoc hd
  intro j hj
  intro a b c hab hbc hac
  by_cases heq : a = c
  · subst c
    have hba : b = a := le_antisymm hbc hab
    subst b
    have hzero := hLift.diag a
    rw [hzero]
    exact ⟨(hpos j hj.1).le, (hpos j hj.1).le⟩
  have hactiveAC := canonicalActive_of_close_ne
    hpos hS hd hj a c heq hac
  have hA := canonicalAnchor_close_active
    hpos hS hd hj a hactiveAC.1
  have hC := canonicalAnchor_close_active
    hpos hS hd hj c hactiveAC.2
  let anchor := canonicalInsertionAnchor hpos hS hd
  have hAnchors : d (anchor a) (anchor c) ≤ j :=
    canonicalAnchors_close_of_close hpos hS hd hj
      hLift a c hactiveAC.1 hactiveAC.2 hac
  have hOrdAB : anchor a ≤ anchor b :=
    canonicalInsertionAnchor_mono hpos hS hd a b hab
  have hOrdBC : anchor b ≤ anchor c :=
    canonicalInsertionAnchor_mono hpos hS hd b c hbc
  have hSplit : d (anchor a) (anchor b) ≤ j ∧
      d (anchor b) (anchor c) ≤ j :=
    hconv j hj (anchor a) (anchor b) (anchor c)
      hOrdAB hOrdBC hAnchors
  have hActB : canonicalActiveAtJump hpos hS hd j b := by
    cases b with
    | inl y => exact trivial
    | inr tag =>
        change canonicalTagLevel tag ≤ j
        by_contra hn
        have hgt : j < canonicalTagLevel tag := lt_of_not_ge hn
        let J : PositiveJumpLevel S := ⟨j, hj⟩
        let finalTag : CanonicalJumpTag hpos hS hd :=
          canonicalClosureTag hpos hS hd J (anchor a)
        have hAnchorB : d (canonicalClassLast hpos hS hd tag)
            (anchor a) ≤ j := by
          change d (anchor (Sum.inr tag)) (anchor a) ≤ j
          rw [hd.symm (anchor (Sum.inr tag)) (anchor a)]
          exact hSplit.1
        have hAfter := canonicalInsertion_higher_tag_after_of_anchor
          hpos hS hd J (anchor a) tag hgt hAnchorB
        have hJtoA : canonicalDistance hpos hS hd
            (.inr finalTag) (.inl (anchor a)) ≤ j := by
          change canonicalDistance hpos hS hd
            (.inr (canonicalClosureTag hpos hS hd J (anchor a)))
            (.inl (anchor a)) ≤ j
          rw [canonicalClosureTag_distance hpos hS hd J (anchor a)]
        have hAtoC : canonicalDistance hpos hS hd
            (.inl (anchor a)) c ≤ j :=
          metric_jump_threshold_trans hpos hS hLift
            (Or.inr hj) (.inl (anchor a)) a c hA hac
        have hFinalC : canonicalDistance hpos hS hd
            (.inr finalTag) c ≤ j :=
          metric_jump_threshold_trans hpos hS hLift
            (Or.inr hj) (.inr finalTag) (.inl (anchor a)) c
              hJtoA hAtoC
        have hCBefore : c ≤ (Sum.inr finalTag :
            V ⊕ CanonicalJumpTag hpos hS hd) :=
          canonicalInsertion_closure_last_of_threshold
            hpos hS hd finalTag c hFinalC
        have hBBefore : (Sum.inr tag :
            V ⊕ CanonicalJumpTag hpos hS hd) ≤ Sum.inr finalTag :=
          le_trans hbc hCBefore
        exact (not_lt_of_ge hBBefore) hAfter
  have hB := canonicalAnchor_close_active hpos hS hd hj b hActB
  have hARev : canonicalDistance hpos hS hd a
      (.inl (anchor a)) ≤ j := by
    calc
      canonicalDistance hpos hS hd a (.inl (anchor a)) =
        canonicalDistance hpos hS hd (.inl (anchor a)) a :=
          hLift.symm _ _
      _ ≤ j := hA
  have hBRev : canonicalDistance hpos hS hd b
      (.inl (anchor b)) ≤ j := by
    calc
      canonicalDistance hpos hS hd b (.inl (anchor b)) =
        canonicalDistance hpos hS hd (.inl (anchor b)) b :=
          hLift.symm _ _
      _ ≤ j := hB
  have hOldAB : canonicalDistance hpos hS hd
      (.inl (anchor a)) (.inl (anchor b)) ≤ j := by
    simpa only [canonicalDistance_old] using hSplit.1
  have hOldBC : canonicalDistance hpos hS hd
      (.inl (anchor b)) (.inl (anchor c)) ≤ j := by
    simpa only [canonicalDistance_old] using hSplit.2
  have hAtoAnchorB : canonicalDistance hpos hS hd a
      (.inl (anchor b)) ≤ j :=
    metric_jump_threshold_trans hpos hS hLift
      (Or.inr hj) a (.inl (anchor a)) (.inl (anchor b))
      hARev hOldAB
  have hAB : canonicalDistance hpos hS hd a b ≤ j :=
    metric_jump_threshold_trans hpos hS hLift
      (Or.inr hj) a (.inl (anchor b)) b hAtoAnchorB hB
  have hBtoAnchorC : canonicalDistance hpos hS hd b
      (.inl (anchor c)) ≤ j :=
    metric_jump_threshold_trans hpos hS hLift
      (Or.inr hj) b (.inl (anchor b)) (.inl (anchor c))
      hBRev hOldBC
  have hBC : canonicalDistance hpos hS hd b c ≤ j :=
    metric_jump_threshold_trans hpos hS hLift
      (Or.inr hj) b (.inl (anchor c)) c hBtoAnchorC hC
  exact ⟨hAB, hBC⟩


/-- The exact paper-facing finite-S metric-order conclusion.
If the original order is convex for every inclusion-maximal
no-jump four-values block B of the manuscript, then the canonical
metric extension on original vertices plus one quotient-class
closure vertex per proper jump has the same block-convex order.

The proof reuses the already checked literal paper-block ↔ jump-cut
equivalence and the full canonical jump-convexity theorem. No
comparison of two different block partitions is assumed. -/
theorem canonicalLift_paperBlockConvex {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (hpaper : PaperBlockConvex S d) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      PaperBlockConvex S (canonicalDistance hpos hS hd)) := by
  letI : LinearOrder (V ⊕ CanonicalJumpTag hpos hS hd) :=
    canonicalInsertionLinearOrder hpos hS hd
  have h4 : FourValues S :=
    fourValues_of_associativeOn hpos hS hassoc
  have hOrig : JumpConvex S d :=
    (paperBlockConvex_iff_jumpConvex hfin hpos h4 hd).mp hpaper
  have hLift : JumpConvex S (canonicalDistance hpos hS hd) :=
    canonicalLift_jumpConvex hfin hpos hS hassoc hd hOrig
  exact (paperBlockConvex_iff_jumpConvex
    hfin hpos h4 (canonicalDistance_metric hfin hpos hS hassoc hd)).mpr hLift

end AllThoseRamseyClasses.Applications.MetricSaturation
