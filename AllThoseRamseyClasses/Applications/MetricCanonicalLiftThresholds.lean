import AllThoseRamseyClasses.Applications.MetricCanonicalDistance

/-!
# Jump thresholds in the canonical finite metric closure

The paper's convex order condition is expressed by all equivalence
relations d(x,y) ≤ j at positive proper jumps j of S.

A short useful algebraic fact follows from the rounded jump identity
j ⊕ j = j: for any two permitted values a,b in S ∪ {0},

  (a ⊕ b ≤ j) ↔ (a ≤ j ∧ b ≤ j).

For three operands the same condition holds componentwise.
Applying these facts to the verified canonicalDistance on the
duplicate-free tag carrier identifies the exact threshold relation:
* original/new: the tag level is at most j and its root lies in
  the same original j-equivalence class;
* new/new for *distinct* tags: both tag levels are at most j
  and their original roots belong to one j-equivalence class.

These formulas are the algebraic description of enlarged jump
classes needed for proving the paper's extended-order convexity.
They do not assume a particular insertion order and do not
themselves constitute an order or Ramsey proof.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- An allowed rounded sum lies below an idempotent positive
jump exactly when each of the two operands lies below it.
Zero is an allowed operand and is handled by the real
neutral-zero extension, not by inventing distance 0 in S. -/
theorem sumWithZero_le_jump_iff {S : Set ℝ}
    (hpos : Positive S)
    {j : ℝ} (hj : Jump S j)
    {a b : ℝ} (ha : a = 0 ∨ a ∈ S)
    (hb : b = 0 ∨ b ∈ S) :
    sumWithZero S a b ≤ j ↔ a ≤ j ∧ b ≤ j := by
  have hleft := le_sumWithZero_left hpos ha hb
  have hright := le_sumWithZero_right hpos ha hb
  have hjid : sumWithZero S j j = j := by
    rw [sumWithZero_eq_distanceSum hpos hj.1 hj.1]
    exact hj.2.2
  constructor
  · intro hab
    exact ⟨hleft.trans hab, hright.trans hab⟩
  · rintro ⟨haj, hbj⟩
    calc
      sumWithZero S a b ≤ sumWithZero S j b :=
        sumWithZero_mono_left hpos ha (Or.inr hj.1) hb haj
      _ ≤ sumWithZero S j j :=
        sumWithZero_mono_right hpos (Or.inr hj.1) hb
          (Or.inr hj.1) hbj
      _ = j := hjid

/-- The corresponding exact jump threshold formula for three
rounded operands, relying only on the already checked
neutral-zero semigroup closure. -/
theorem sumWithZero_triple_le_jump_iff {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {j : ℝ} (hj : Jump S j)
    {a b c : ℝ} (ha : a = 0 ∨ a ∈ S)
    (hb : b = 0 ∨ b ∈ S)
    (hc : c = 0 ∨ c ∈ S) :
    sumWithZero S (sumWithZero S a b) c ≤ j ↔
      a ≤ j ∧ b ≤ j ∧ c ≤ j := by
  have hab := sumWithZero_mem hpos hS ha hb
  rw [sumWithZero_le_jump_iff hpos hj hab hc,
    sumWithZero_le_jump_iff hpos hj ha hb]
  tauto

/-- In the canonical enlarged metric, a closure vertex is
j-close to an original vertex exactly when (1) its own
positive jump level is at most j and (2) its chosen
representative is j-close to that original vertex. -/
theorem canonicalDistance_closure_old_le_jump_iff {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {V : Type u} {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd)
    (x : V) {j : ℝ} (hj : Jump S j) :
    canonicalDistance hpos hS hd (.inr tag) (.inl x) ≤ j ↔
      canonicalTagLevel tag ≤ j ∧
      d (canonicalTagRoot tag) x ≤ j := by
  rw [canonicalDistance_new_old]
  exact sumWithZero_le_jump_iff hpos hj
    (Or.inr (canonicalTagLevel_jump tag).1)
    (metric_value_mem hd (canonicalTagRoot tag) x)

/-- For two *distinct* canonical closure vertices, the
extended metric puts them within jump radius j precisely
when both tag levels are at most j and their original
root representatives are j-equivalent. This statement
does not need the original vertex set to be finite. -/
theorem canonicalDistance_closure_closure_le_jump_iff {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {V : Type u} {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd) (hab : a ≠ b)
    {j : ℝ} (hj : Jump S j) :
    canonicalDistance hpos hS hd (.inr a) (.inr b) ≤ j ↔
      canonicalTagLevel a ≤ j ∧
      d (canonicalTagRoot a) (canonicalTagRoot b) ≤ j ∧
      canonicalTagLevel b ≤ j := by
  rw [canonicalDistance_new_new hpos hS hd a b hab]
  exact sumWithZero_triple_le_jump_iff hpos hS hj
    (Or.inr (canonicalTagLevel_jump a).1)
    (metric_value_mem hd (canonicalTagRoot a) (canonicalTagRoot b))
    (Or.inr (canonicalTagLevel_jump b).1)

/-- The jump relation on the diagonal of a closure tag is
automatically true: it is a genuine metric diagonal, not
the positive double-sandwich label. -/
theorem canonicalDistance_closure_diag_le_jump {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {V : Type u} {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd)
    {j : ℝ} (hj : Jump S j) :
    canonicalDistance hpos hS hd (.inr tag) (.inr tag) ≤ j := by
  rw [canonicalDistance_new_diag]
  exact (hpos j hj.1).le

end AllThoseRamseyClasses.Applications.MetricSaturation
