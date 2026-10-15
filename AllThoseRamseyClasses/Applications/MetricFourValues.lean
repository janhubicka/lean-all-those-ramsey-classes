import AllThoseRamseyClasses.Applications.MetricFiniteGeneration

/-!
# The four-values condition and finite distance reduction

`FourValues` is the manuscript's literal pair-of-triangles condition.
For positive allowed distances with well-defined rounded sums it is
proved equivalent to associativity. No topological closedness or
largest-side restriction is added. The final result gives finite
four-values extensions of finite distance sets under the original
four-values hypotheses. It does not assert a metric Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The three ordinary real triangle inequalities, with equality allowed. -/
def Triangle (a b c : ℝ) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b

/-- The manuscript's four-values condition, including all four side orderings. -/
def FourValues (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    (∃ x ∈ S, Triangle a b x ∧ Triangle c d x) →
    ∃ y ∈ S, Triangle a c y ∧ Triangle b d y

private theorem triangle_swap {a b c : ℝ} (h : Triangle a b c) :
    Triangle b a c :=
  ⟨h.2.1, h.1, by simpa only [add_comm] using h.2.2⟩

/-- An allowed candidate is below the actual rounded sum. -/
theorem le_distanceSum_of_le_add {S : Set ℝ} {s a b : ℝ}
    (hs : s ∈ S) (hle : s ≤ a + b) : s ≤ distanceSum S a b := by
  exact le_csSup ⟨a + b, fun _ ht => ht.2⟩ ⟨hs, hle⟩

/-- Monotonicity of the rounded sum on a nonempty candidate set. -/
theorem distanceSum_mono_right {S : Set ℝ} {a b c : ℝ}
    (ha : a ∈ S) (hb : 0 ≤ b) (hbc : b ≤ c) :
    distanceSum S a b ≤ distanceSum S a c := by
  have hne : {s : ℝ | s ∈ S ∧ s ≤ a + b}.Nonempty :=
    ⟨a, ha, by linarith⟩
  apply csSup_le hne
  intro s hs
  exact le_distanceSum_of_le_add hs.1 (by linarith [hs.2])

/-- Two allowed positive sides form a triangle with their rounded sum. -/
theorem triangle_distanceSum {S : Set ℝ} (hpos : Positive S)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    Triangle a b (distanceSum S a b) := by
  have hleft := left_le_distanceSum ha (hpos b hb).le
  have hright : b ≤ distanceSum S a b := by
    rw [distanceSum_comm S a b]
    exact left_le_distanceSum hb (hpos a ha).le
  exact ⟨by linarith [hpos b hb], by linarith [hpos a ha],
    distanceSum_le_add ha (hpos b hb).le⟩

private theorem cross_bound {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S)
    {a b c d x : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (hx : x ∈ S)
    (hbax : b ≤ a + x) (hxcd : x ≤ c + d) :
    b ≤ d + distanceSum S a c := by
  calc
    b ≤ distanceSum S a x := le_distanceSum_of_le_add hb hbax
    _ ≤ distanceSum S a (distanceSum S c d) :=
      distanceSum_mono_right ha (hpos x hx).le (le_distanceSum_of_le_add hx hxcd)
    _ = distanceSum S (distanceSum S a c) d := (hassoc a ha c hc d hd).symm
    _ ≤ distanceSum S a c + d := distanceSum_le_add (hS a ha c hc) (hpos d hd).le
    _ = d + distanceSum S a c := add_comm _ _

private theorem cross_triangle {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S)
    {a b c d x : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (hx : x ∈ S)
    (h1 : Triangle a b x) (h2 : Triangle c d x)
    (hle : distanceSum S a c ≤ distanceSum S b d) :
    Triangle b d (distanceSum S a c) := by
  refine ⟨cross_bound hpos hS hassoc ha hb hc hd hx h1.2.1 h2.2.2, ?_, ?_⟩
  · simpa only [distanceSum_comm S c a] using
      cross_bound hpos hS hassoc hc hd ha hb hx h2.2.1 h1.2.2
  · exact hle.trans (distanceSum_le_add hb (hpos d hd).le)

/-- Associativity supplies the missing diagonal in the literal four-values condition. -/
theorem fourValues_of_associativeOn {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S) :
    FourValues S := by
  intro a ha b hb c hc d hd hex
  obtain ⟨x, hx, h1, h2⟩ := hex
  rcases le_total (distanceSum S a c) (distanceSum S b d) with hle | hle
  · exact ⟨distanceSum S a c, hS a ha c hc, triangle_distanceSum hpos ha hc,
      cross_triangle hpos hS hassoc ha hb hc hd hx h1 h2 hle⟩
  · exact ⟨distanceSum S b d, hS b hb d hd,
      cross_triangle hpos hS hassoc hb ha hd hc hx
        (triangle_swap h1) (triangle_swap h2) hle,
      triangle_distanceSum hpos hb hd⟩

private theorem associative_le_of_fourValues {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (h4 : FourValues S)
    {a b c : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    distanceSum S (distanceSum S a b) c ≤ distanceSum S a (distanceSum S b c) := by
  let x := distanceSum S a b
  let y := distanceSum S x c
  have hx : x ∈ S := hS a ha b hb
  have hy : y ∈ S := hS x hx c hc
  have hxy := triangle_distanceSum hpos hx hc
  have hycx : Triangle y c x := by
    exact ⟨by linarith [hxy.2.2], by linarith [hxy.2.1], by linarith [hxy.1]⟩
  obtain ⟨t, ht, hat, hbt⟩ :=
    h4 a ha b hb y hy c hc ⟨x, hx, triangle_distanceSum hpos ha hb, hycx⟩
  have htbc := le_distanceSum_of_le_add ht hbt.2.2
  exact le_distanceSum_of_le_add hy (by linarith [hat.2.1])

/-- The four-values hypothesis itself implies associativity of the actual rounded sum. -/
theorem associativeOn_of_fourValues {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (h4 : FourValues S) :
    AssociativeOn S := by
  intro a ha b hb c hc
  apply le_antisymm (associative_le_of_fourValues hpos hS h4 ha hb hc)
  calc
    distanceSum S a (distanceSum S b c) = distanceSum S (distanceSum S c b) a := by
      rw [distanceSum_comm S b c]
      exact distanceSum_comm S a (distanceSum S c b)
    _ ≤ distanceSum S c (distanceSum S b a) :=
      associative_le_of_fourValues hpos hS h4 hc hb ha
    _ = distanceSum S (distanceSum S a b) c := by
      rw [distanceSum_comm S b a]
      exact distanceSum_comm S c (distanceSum S a b)

/-- Exact scalar equivalence used in the manuscript, without extra closedness. -/
theorem associativeOn_iff_fourValues {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) :
    AssociativeOn S ↔ FourValues S :=
  ⟨fourValues_of_associativeOn hpos hS, associativeOn_of_fourValues hpos hS⟩

/-- Finite distance reduction on the original four-values hypotheses.
The finite extension has its own well-defined rounded sum and four-values property. -/
theorem exists_finite_fourValues_extension {S D : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (h4 : FourValues S)
    (hD : D.Finite) (hDS : D ⊆ S) :
    ∃ T : Set ℝ, T.Finite ∧ D ⊆ T ∧ T ⊆ S ∧
      WellDefined T ∧ FourValues T := by
  obtain ⟨T, hT, hDT, hTS, hTw, hTa⟩ :=
    exists_finite_distance_extension hpos hS
      (associativeOn_of_fourValues hpos hS h4) hD hDS
  exact ⟨T, hT, hDT, hTS, hTw,
    fourValues_of_associativeOn (fun t ht => hpos t (hTS ht)) hTw hTa⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
