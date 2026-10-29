import AllThoseRamseyClasses.Applications.MetricFourValues

/-!
# Absorbed prefix levels are invariant under bounded replacement paths

The replacement clause of the printed `lem:Sequivalence` claims that
replacing an unimportant path P by ANY path whose edge lengths are
bounded by a member of the same block leaves the relevant rounded
prefix length unchanged and hence preserves a nonmetric closing edge.

The elementary and independent part can be phrased without any
finite-S, associativity, or block assumptions:

If a is an allowed rounded prefix length and a absorbs an allowed
threshold q (a ⊕ q = a), then a absorbs EVERY allowed distance e ≤ q.
Consequently folding ANY finite replacement path with all edges
≤ q from initial prefix a returns exactly a. A closing edge d>a
therefore still violates the rounded path inequality.

This makes the next true mathematical obstruction precise: deduce
a ⊕ max(B(P)) = a from the published definition of an unimportant
path (constant rounded prefix) and the actual finite four-values
block B(P). Neither this block-absorption bridge nor the complete
compressed-cycle construction is proved here. These lemmas do NOT
silently assume the cycle theorem, numerical cutoff, or Ramsey arrow.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Monotonicity gives downward closure of a fixed absorption
threshold in the rounded distance semigroup. -/
theorem roundedAbsorbs_of_le
    {S : Set ℝ} (hpos : Positive S)
    {a q e : ℝ}
    (ha : a ∈ S) (he : e ∈ S)
    (heq : e ≤ q)
    (hAbs : distanceSum S a q = a) :
    distanceSum S a e = a := by
  have hmono : distanceSum S a e ≤ a := by
    calc
      distanceSum S a e ≤ distanceSum S a q :=
        distanceSum_mono_right ha (hpos e he).le heq
      _ = a := hAbs
  exact le_antisymm hmono
    (left_le_distanceSum ha (hpos e he).le)

/-- No associativity is needed: every step along a bounded
replacement path stays at the same absorbed starting prefix. -/
theorem roundedFoldl_eq_of_absorbed_bound
    {S : Set ℝ} (hpos : Positive S)
    {a q : ℝ} (ha : a ∈ S)
    (hAbs : distanceSum S a q = a)
    (edges : List ℝ)
    (hEdges : ∀ e ∈ edges, e ∈ S ∧ e ≤ q) :
    edges.foldl (distanceSum S) a = a := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
      have he : e ∈ S := (hEdges e (by simp)).1
      have heq : e ≤ q := (hEdges e (by simp)).2
      have hStep : distanceSum S a e = a :=
        roundedAbsorbs_of_le hpos ha he heq hAbs
      have hTail : ∀ t ∈ es, t ∈ S ∧ t ≤ q := by
        intro t ht
        exact hEdges t (by simp [ht])
      simpa only [List.foldl_cons, hStep] using ih hTail

/-- The obstruction represented by a closing edge strictly larger
than the previous path prefix survives any such replacement. -/
theorem roundedBadClosingEdge_persists_of_absorbed_bound
    {S : Set ℝ} (hpos : Positive S)
    {a q d : ℝ} (ha : a ∈ S)
    (hAbs : distanceSum S a q = a)
    (hBad : a < d)
    (replacement : List ℝ)
    (hReplacement : ∀ e ∈ replacement, e ∈ S ∧ e ≤ q) :
    replacement.foldl (distanceSum S) a < d := by
  rw [roundedFoldl_eq_of_absorbed_bound
    hpos ha hAbs replacement hReplacement]
  exact hBad

/-- Every rounded step increases (or preserves) an allowed
prefix: the rounded value is at least its previous value.
This lemma does not assume associativity. -/
theorem roundedFoldl_start_le
    {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S)
    {a : ℝ} (ha : a ∈ S)
    (edges : List ℝ)
    (hEdges : ∀ e ∈ edges, e ∈ S) :
    a ≤ edges.foldl (distanceSum S) a := by
  induction edges generalizing a with
  | nil => simp
  | cons e es ih =>
      have he : e ∈ S := hEdges e (by simp)
      have hTail : ∀ t ∈ es, t ∈ S := by
        intro t ht
        exact hEdges t (by simp [ht])
      calc
        a ≤ distanceSum S a e :=
          left_le_distanceSum ha (hpos e he).le
        _ ≤ es.foldl (distanceSum S) (distanceSum S a e) :=
          ih (hS a ha e he) hTail

/-- In a constant-prefix ('unimportant') path, EACH individual
edge is absorbed by the original prefix. No assumption about
which block its edge lengths occupy is used here. Together
with the separate plateau-to-proper-jump theorem this provides
the missing source step before block-bounded replacement. -/
theorem roundedFoldl_plateau_absorbs_each_edge
    {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S)
    {a : ℝ} (ha : a ∈ S)
    (edges : List ℝ) :
    (∀ e ∈ edges, e ∈ S) →
    edges.foldl (distanceSum S) a = a →
    ∀ e ∈ edges, distanceSum S a e = a := by
  induction edges with
  | nil =>
      intro _ _ e he
      simp at he
  | cons e es ih =>
      intro hEdges hFinal
      have he : e ∈ S := hEdges e (by simp)
      have hTail : ∀ t ∈ es, t ∈ S := by
        intro t ht
        exact hEdges t (by simp [ht])
      have hmono : distanceSum S a e ≤
          es.foldl (distanceSum S) (distanceSum S a e) :=
        roundedFoldl_start_le hpos hS (hS a ha e he) es hTail
      have hStart : a ≤ distanceSum S a e :=
        left_le_distanceSum ha (hpos e he).le
      have hStep : distanceSum S a e = a := by
        apply le_antisymm ?_ hStart
        calc
          distanceSum S a e ≤
              es.foldl (distanceSum S) (distanceSum S a e) := hmono
          _ = a := by simpa only [List.foldl_cons] using hFinal
      have hRest : es.foldl (distanceSum S) a = a := by
        simpa only [List.foldl_cons, hStep] using hFinal
      have hTailAbs := ih hTail hRest
      intro t ht
      rcases List.mem_cons.mp ht with hte | ht
      · subst t
        exact hStep
      · exact hTailAbs t ht

end AllThoseRamseyClasses.Applications.MetricSaturation
