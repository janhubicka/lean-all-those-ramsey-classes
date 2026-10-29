import AllThoseRamseyClasses.Applications.MetricBlockPathAbsorption
import AllThoseRamseyClasses.Applications.MetricFiniteWellDefined
import Mathlib.Tactic

/-!
# Explicit prefix compression for the path opposite a nonmetric closing edge

In the printed `lem:Sequivalence`, orient a nonmetric cycle with a
closing edge d and an opposite path starting with its first edge a.
The remaining edges are processed by rounded prefixes. At each edge
we either keep it (when the rounded prefix strictly increases) or
discard it (when the edge leaves the rounded prefix unchanged).

This file constructs the ACTUAL list of kept edges, proves that it
has exactly the same final rounded length as the original tail, and
bounds the number of kept edges by the number of distinct allowed
prefix levels strictly below the incompatible closing edge d.

In particular, for finite S and a strictly too-long closing edge,
there are at most |S|-2 kept later edges, giving at most |S|
vertices on the compressed cycle. In the exceptional case where
there are no kept later edges, the paper retains one original
absorbed edge to make a genuine triangle; the resulting bound
is max(3,|S|).

The translation from this edge-list process to the actual cycle
obtained by contracting disjoint maximal constant-prefix paths,
with all boundary vertices and the exact arbitrary-replacement
support count, is NOT claimed in this module. It also does not
assert weak local completion or a Ramsey arrow.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Keep exactly those later path edges on which the rounded prefix
strictly increases. A plateau edge is deleted. This constructs the
path-compression EDGE DATA, not an abstract assumed quotient bound. -/
noncomputable def risingPrefixEdges
    (S : Set ℝ) (a : ℝ) : List ℝ → List ℝ
  | [] => []
  | e :: es => by
      classical
      exact if distanceSum S a e = a then
        risingPrefixEdges S a es
      else e :: risingPrefixEdges S (distanceSum S a e) es

/-- Deleting exactly the absorbed edges preserves the ENTIRE rounded
path length, even if S is infinite and no associativity is assumed. -/
theorem risingPrefixEdges_foldl
    (S : Set ℝ) (edges : List ℝ) (a : ℝ) :
    (risingPrefixEdges S a edges).foldl (distanceSum S) a =
      edges.foldl (distanceSum S) a := by
  induction edges generalizing a with
  | nil => rfl
  | cons e es ih =>
      classical
      by_cases h : distanceSum S a e = a
      · simp only [risingPrefixEdges, if_pos h, List.foldl_cons]
        rw [h]
        exact ih a
      · simp only [risingPrefixEdges, if_neg h, List.foldl_cons]
        exact ih (distanceSum S a e)

/-- The finite set of allowed prefix levels between a and d.
Its cardinal decreases when a strictly increases, because the
old prefix a belongs to the old set but not the new one. -/
noncomputable def prefixLevelsBelow
    (S : Set ℝ) (hfin : S.Finite) (a d : ℝ) : Finset ℝ := by
  classical
  exact hfin.toFinset.filter (fun t => a ≤ t ∧ t < d)

/-- Exact membership statement for the rank used in the compression. -/
theorem mem_prefixLevelsBelow
    (S : Set ℝ) (hfin : S.Finite) (a d t : ℝ) :
    t ∈ prefixLevelsBelow S hfin a d ↔
      t ∈ S ∧ a ≤ t ∧ t < d := by
  classical
  simp [prefixLevelsBelow, hfin.mem_toFinset]

/-- Raising the rounded prefix from a to b>a consumes at
least one distinct allowed prefix level below d. -/
theorem prefixLevelsBelow_card_strict
    (S : Set ℝ) (hfin : S.Finite)
    {a b d : ℝ}
    (ha : a ∈ S) (had : a < d) (hab : a < b) :
    (prefixLevelsBelow S hfin b d).card + 1 ≤
      (prefixLevelsBelow S hfin a d).card := by
  classical
  let A := prefixLevelsBelow S hfin a d
  let B := prefixLevelsBelow S hfin b d
  have hBsubA : B ⊆ A := by
    intro t ht
    obtain ⟨htS, hbt, htd⟩ :=
      (mem_prefixLevelsBelow S hfin b d t).mp ht
    exact (mem_prefixLevelsBelow S hfin a d t).mpr
      ⟨htS, (le_of_lt hab).trans hbt, htd⟩
  have haA : a ∈ A :=
    (mem_prefixLevelsBelow S hfin a d a).mpr
      ⟨ha, le_refl a, had⟩
  have haNotB : a ∉ B := by
    intro h
    have hba := ((mem_prefixLevelsBelow S hfin b d a).mp h).2.1
    exact (not_le_of_gt hab) hba
  have hInsert : insert a B ⊆ A := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact haA
    · exact hBsubA ht
  have hCard := Finset.card_le_card hInsert
  have hCardInsert : (insert a B).card = B.card + 1 :=
    Finset.card_insert_of_notMem haNotB
  omega

/-- The closing-edge value d is *not* one of the available
rounded prefix levels strictly below d, so their total count
is at most |S|-1, even when a is not the least distance. -/
theorem prefixLevelsBelow_card_add_one_le_card
    (S : Set ℝ) (hfin : S.Finite)
    {a d : ℝ} (hd : d ∈ S) :
    (prefixLevelsBelow S hfin a d).card + 1 ≤
      hfin.toFinset.card := by
  classical
  let A := prefixLevelsBelow S hfin a d
  have hdNotA : d ∉ A := by
    intro h
    have hdd := ((mem_prefixLevelsBelow S hfin a d d).mp h).2.2
    exact (lt_irrefl d) hdd
  have hInsert : insert d A ⊆ hfin.toFinset := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hfin.mem_toFinset.mpr hd
    · have htS := ((mem_prefixLevelsBelow S hfin a d t).mp ht).1
      exact hfin.mem_toFinset.mpr htS
  have hCard := Finset.card_le_card hInsert
  have hCardInsert : (insert d A).card = A.card + 1 :=
    Finset.card_insert_of_notMem hdNotA
  omega

/-- Every retained rising edge consumes one allowed strict prefix
level below d. Includes an empty original tail and duplicate
distances. The limit only uses the final bad-edge inequality. -/
theorem risingPrefixEdges_length_add_one_le_levels
    (S : Set ℝ) (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S) (d : ℝ)
    (edges : List ℝ) :
    ∀ a : ℝ, a ∈ S → a < d →
      (∀ e ∈ edges, e ∈ S) →
      edges.foldl (distanceSum S) a < d →
      (risingPrefixEdges S a edges).length + 1 ≤
        (prefixLevelsBelow S hfin a d).card := by
  induction edges with
  | nil =>
      intro a ha had _ _
      have hA : a ∈ prefixLevelsBelow S hfin a d :=
        (mem_prefixLevelsBelow S hfin a d a).mpr
          ⟨ha, le_refl a, had⟩
      have hCard : 1 ≤ (prefixLevelsBelow S hfin a d).card :=
        Finset.one_le_card.mpr ⟨a, hA⟩
      simpa [risingPrefixEdges] using hCard
  | cons e es ih =>
      intro a ha had hEdges hFinal
      have he : e ∈ S := hEdges e (by simp)
      have hTail : ∀ t ∈ es, t ∈ S := by
        intro t ht
        exact hEdges t (by simp [ht])
      let b : ℝ := distanceSum S a e
      have hb : b ∈ S := hS a ha e he
      have hab : a ≤ b :=
        left_le_distanceSum ha (hpos e he).le
      have hTailFinal : es.foldl (distanceSum S) b < d := by
        simpa only [List.foldl_cons, b] using hFinal
      have hbLtD : b < d :=
        lt_of_le_of_lt
          (roundedFoldl_start_le hpos hS hb es hTail)
          hTailFinal
      by_cases hEq : b = a
      · have hTailSame : es.foldl (distanceSum S) a < d := by
          simpa only [hEq] using hTailFinal
        have hIH := ih a ha had hTail hTailSame
        have hKeep : risingPrefixEdges S a (e :: es) =
            risingPrefixEdges S a es := by
          have h : distanceSum S a e = a := hEq
          simp [risingPrefixEdges, h]
        simpa only [hKeep] using hIH
      · have hlt : a < b := lt_of_le_of_ne hab (Ne.symm hEq)
        have hIH := ih b hb hbLtD hTail hTailFinal
        have hStrict :=
          prefixLevelsBelow_card_strict S hfin ha had hlt
        have hKeep : risingPrefixEdges S a (e :: es) =
            e :: risingPrefixEdges S b es := by
          have h : distanceSum S a e ≠ a := hEq
          simp [risingPrefixEdges, h, b]
        rw [hKeep]
        simp only [List.length_cons]
        omega

/-- The true number of rising edges in a bad path is bounded
by |S|-2. Thus the ordinary compressed cycle, retaining its
first edge and its incompatible closing edge, has at most
|S| vertices. -/
theorem risingPrefixEdges_compressed_cycle_card
    (S : Set ℝ) (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {a d : ℝ} (ha : a ∈ S) (hd : d ∈ S)
    (had : a < d) (edges : List ℝ)
    (hEdges : ∀ e ∈ edges, e ∈ S)
    (hBad : edges.foldl (distanceSum S) a < d) :
    (risingPrefixEdges S a edges).length + 2 ≤
      hfin.toFinset.card := by
  have hRank :=
    risingPrefixEdges_length_add_one_le_levels
      S hfin hpos hS d edges a ha had hEdges hBad
  have hSCard :=
    prefixLevelsBelow_card_add_one_le_card S hfin hd
      (a := a)
  omega

/-- The corrected numeric upper bound max(3,|S|) accounts for
the exceptional single-plateau case: when no later edge rises,
retain any ONE absorbed original edge to obtain a triangle.
No claim about the actual quotient's geometric embedding is made. -/
theorem risingPrefixEdges_corrected_cycle_card
    (S : Set ℝ) (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {a d : ℝ} (ha : a ∈ S) (hd : d ∈ S)
    (had : a < d) (edges : List ℝ)
    (hEdges : ∀ e ∈ edges, e ∈ S)
    (hBad : edges.foldl (distanceSum S) a < d) :
    max 3 ((risingPrefixEdges S a edges).length + 2) ≤
      max 3 hfin.toFinset.card := by
  exact max_le_max (le_refl 3)
    (risingPrefixEdges_compressed_cycle_card
      S hfin hpos hS ha hd had edges hEdges hBad)

/-- In the exceptional case of NO strictly rising later edges,
the whole original tail is unimportant. If it contains at least
one actual edge, retaining just its first original edge leaves a
two-edge opposite path whose rounded length is still smaller
than the closing edge: the exceptional compressed triangle. -/
theorem risingPrefixEdges_exceptional_triangle
    (S : Set ℝ) (hpos : Positive S) (hS : WellDefined S)
    {a d : ℝ} (ha : a ∈ S) (had : a < d)
    (edges : List ℝ) (hne : edges ≠ [])
    (hEdges : ∀ e ∈ edges, e ∈ S)
    (hNoRises : risingPrefixEdges S a edges = []) :
    ∃ e ∈ edges, distanceSum S a e = a ∧
      distanceSum S a e < d := by
  have hPlateau : edges.foldl (distanceSum S) a = a := by
    rw [← risingPrefixEdges_foldl S edges a, hNoRises]
    rfl
  cases edges with
  | nil => contradiction
  | cons e es =>
      have he : e ∈ e :: es := by simp
      have hAbs :
          distanceSum S a e = a :=
        roundedFoldl_plateau_absorbs_each_edge
          hpos hS ha (e :: es) hEdges hPlateau e he
      exact ⟨e, he, hAbs, by simpa [hAbs] using had⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
