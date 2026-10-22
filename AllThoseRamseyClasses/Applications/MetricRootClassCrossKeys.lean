import AllThoseRamseyClasses.Applications.MetricRootClassKeys

/-!
# Cross-side equality of ordered class keys detects only shared root classes

The one-jump metric order key has independent priorities 0 and 1
for private classes on the two sides, but priority 2 for classes
meeting a shared root class. Equality of two keys, one from each
side, therefore means that BOTH class labels equal the images of
the SAME root class. No private class can acquire an accidental
equal key, even if the number of earlier root classes agrees.

This is the missing algebraic half of the convex metric
amalgamation: together with the exact rooted S-metric j-class
decomposition (#557/#560/#564), it can turn key equality into
genuine metric j-equivalence. For all jump levels simultaneously,
the nested lexicographic key invariant is separate.

No identification of ordinary root VERTEX cuts with class cuts
is made, and no final convex order or auxiliary functional
Ramsey theorem is assumed here.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w

/-- The root CLASS cuts strictly increase along an injectively
ordered list of distinct root classes. -/
private theorem rootClassCut_strict_on_root
    {R : Type u} {K : Type v}
    [Fintype R] [LinearOrder R] [LinearOrder K]
    (root : R → K) (hRoot : StrictMono root)
    {a b : R} (hab : a < b) :
    rootClassCut root id (root a) <
      rootClassCut root id (root b) :=
  rootClassCut_strict_after_root root id a (root b) (hRoot hab)

/-- For opposite-side keys with different private priorities,
equality holds precisely at a COMMON root class. The right
root-class embedding is strictly order preserving, while the
two embeddings are assumed to agree on the root class order. -/
theorem classSideKey_cross_eq_iff_root
    {R : Type u} {K : Type v} {L : Type w}
    [Fintype R] [LinearOrder R]
    [Fintype K] [LinearOrder K]
    [Fintype L] [LinearOrder L]
    (rootLeft : R → K) (rootRight : R → L)
    (hCompat : ∀ a b : R,
      rootLeft a < rootLeft b ↔ rootRight a < rootRight b)
    (hRootRight : StrictMono rootRight)
    (x : K) (y : L) :
    classSideKey rootLeft 0 x = classSideKey rootRight 1 y ↔
      ∃ a : R, rootLeft a = x ∧ rootRight a = y := by
  classical
  constructor
  · intro h
    by_cases hL : ∃ a : R, rootLeft a = x
    · obtain ⟨a, ha⟩ := hL
      have hRootL : ∃ t : R, rootLeft t = x := ⟨a, ha⟩
      by_cases hR : ∃ b : R, rootRight b = y
      · obtain ⟨b, hb⟩ := hR
        have hRootR : ∃ t : R, rootRight t = y := ⟨b, hb⟩
        have hCut :
            rootClassCut rootLeft id x =
              rootClassCut rootRight id y := by
          have hp := congrArg
            (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex z).1) h
          simpa [classSideKey, hRootL, hRootR] using hp
        have hRightCut :
            rootClassCut rootRight id (rootRight a) =
              rootClassCut rootRight id (rootRight b) := by
          calc
            rootClassCut rootRight id (rootRight a) =
                rootClassCut rootLeft id (rootLeft a) :=
              (rootClassCut_root_agree
                rootLeft rootRight hCompat a).symm
            _ = rootClassCut rootRight id (rootRight b) := by
              simpa only [ha, hb] using hCut
        have hab : a = b := by
          rcases lt_trichotomy a b with hlt | heq | hgt
          · have hstrict := rootClassCut_strict_on_root
              rootRight hRootRight hlt
            omega
          · exact heq
          · have hstrict := rootClassCut_strict_on_root
              rootRight hRootRight hgt
            omega
        refine ⟨a, ha, ?_⟩
        rw [hab]
        exact hb
      · have hPriority := congrArg
          (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) =>
            (ofLex (ofLex z).2).1) h
        simp [classSideKey, hRootL, hR] at hPriority
    · by_cases hR : ∃ b : R, rootRight b = y
      · have hPriority := congrArg
          (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) =>
            (ofLex (ofLex z).2).1) h
        simp [classSideKey, hL, hR] at hPriority
      · have hPriority := congrArg
          (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) =>
            (ofLex (ofLex z).2).1) h
        simp [classSideKey, hL, hR] at hPriority
  · rintro ⟨a, rfl, rfl⟩
    exact classSideKey_root_agree
      rootLeft rootRight hCompat a

end AllThoseRamseyClasses.Applications.MetricConvexOrder
