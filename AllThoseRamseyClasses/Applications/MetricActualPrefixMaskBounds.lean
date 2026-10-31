import AllThoseRamseyClasses.Applications.MetricCyclePrefixCompression
import AllThoseRamseyClasses.Applications.MetricPlateauRunSupportCount
import Mathlib.Tactic

/-!
# Actual prefix compression mask and its exposed-vertex cutoff

Combine the two independent kernel-checked pieces of the printed
`lem:Sequivalence`:

* `MetricCyclePrefixCompression` builds the retained strictly
  increasing edge list and proves its length k satisfies k+2 <= |S|;
* `MetricPlateauRunSupportCount` proves that an absorbed-edge
  Boolean mask with k strict entries has at most k+1 maximal
  absorbed runs.

The mask below is computed from the ORIGINAL S-valued edge list
and its genuine rounded running prefix, not supplied as an
unrelated Boolean sequence. We prove its strict-edge count is
EXACTLY the length of the retained list. Hence the corrected
compressed-cycle vertex count q=max(3,k+2), plus the actual
number p of maximal absorbed runs, satisfies q+p<=2|S|,
including the exceptional k=0 case.

In the exceptional k=0 case, the mask is nonempty precisely
when the original tail contains an actual edge; then it
contains exactly one maximal absorbed run. No undefined
zero-edge paper block is introduced.

The actual vertices of the original cycle, quotient by
contraction, and common functional closures on each run
still need a source-matched interpretation. Accordingly
this is an exact source-list counting theorem, NOT a
complete cycle-compression or weak local-completion theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The actual equality test of each later edge against the
rounded prefix achieved by all its predecessors.
`true` means absorbed, `false` means a strict increase. -/
noncomputable def actualPrefixAbsorptionMask
    (S : Set ℝ) (a : ℝ) : List ℝ → List Bool
  | [] => []
  | e :: es => by
      classical
      exact if distanceSum S a e = a then
        true :: actualPrefixAbsorptionMask S a es
      else
        false :: actualPrefixAbsorptionMask S (distanceSum S a e) es

/-- The actual flag mask has exactly one entry per original
later edge, so no path segment is silently added or lost. -/
theorem actualPrefixAbsorptionMask_length
    (S : Set ℝ) (a : ℝ) (edges : List ℝ) :
    (actualPrefixAbsorptionMask S a edges).length = edges.length := by
  induction edges generalizing a with
  | nil => rfl
  | cons e es ih =>
      classical
      by_cases h : distanceSum S a e = a
      · simp [actualPrefixAbsorptionMask, h, ih]
      · simp [actualPrefixAbsorptionMask, h, ih]

/-- Exact match between the strict entries of the ACTUAL
prefix mask and the retained rising-edge list. This is
the essential bridge from algorithmic edge compression
to maximal absorbed-run counting. -/
theorem actualPrefixAbsorptionMask_strictCount
    (S : Set ℝ) (a : ℝ) (edges : List ℝ) :
    prefixStrictEdgeCount (actualPrefixAbsorptionMask S a edges) =
      (risingPrefixEdges S a edges).length := by
  induction edges generalizing a with
  | nil => rfl
  | cons e es ih =>
      classical
      by_cases h : distanceSum S a e = a
      · simp [actualPrefixAbsorptionMask, risingPrefixEdges,
          prefixStrictEdgeCount, h, ih]
      · simp [actualPrefixAbsorptionMask, risingPrefixEdges,
          prefixStrictEdgeCount, h, ih]

/-- Maximal absorbed runs of the REAL S-prefix classification,
not an arbitrarily chosen mask, are bounded by the number
of genuine rising later edges plus one. -/
theorem actualPrefixAbsorptionMask_runCount
    (S : Set ℝ) (a : ℝ) (edges : List ℝ) :
    prefixPlateauRunCount false (actualPrefixAbsorptionMask S a edges) ≤
      (risingPrefixEdges S a edges).length + 1 := by
  have h := (prefixPlateauRunCount_bounds
    (actualPrefixAbsorptionMask S a edges)).1
  rw [actualPrefixAbsorptionMask_strictCount] at h
  exact h

/-- Nonempty absorbed-only masks have precisely one maximal run.
The Boolean statement is independent of metric structure. -/
theorem prefixMask_oneRun_of_noRises
    (flags : List Bool) (hne : flags ≠ [])
    (hNoRises : prefixStrictEdgeCount flags = 0) :
    prefixPlateauRunCount false flags = 1 := by
  cases flags with
  | nil => contradiction
  | cons b bs =>
      cases b with
      | false =>
          simp [prefixStrictEdgeCount] at hNoRises
      | true =>
          have hRest : prefixStrictEdgeCount bs = 0 := by
            simpa [prefixStrictEdgeCount] using hNoRises
          have hBound := (prefixPlateauRunCount_bounds bs).2
          have hZero : prefixPlateauRunCount true bs = 0 := by
            omega
          simpa [prefixPlateauRunCount, hZero]

/-- If the original tail is nonempty and the compression keeps
no later rising edges, exactly ONE nonempty absorbed run exists.
This handles the exceptional n≥3 triangle without constructing
an empty paper block. -/
theorem actualPrefixAbsorptionMask_exceptional_oneRun
    (S : Set ℝ) (a : ℝ) (edges : List ℝ)
    (hne : edges ≠ [])
    (hNoRises : risingPrefixEdges S a edges = []) :
    prefixPlateauRunCount false (actualPrefixAbsorptionMask S a edges) = 1 := by
  have hMaskNonempty : actualPrefixAbsorptionMask S a edges ≠ [] := by
    intro he
    have hLengths := actualPrefixAbsorptionMask_length S a edges
    rw [he] at hLengths
    have hEdgesEmpty : edges = [] := List.length_eq_zero_iff.mp hLengths.symm
    exact hne hEdgesEmpty
  have hMaskNoRises :
      prefixStrictEdgeCount (actualPrefixAbsorptionMask S a edges) = 0 := by
    rw [actualPrefixAbsorptionMask_strictCount, hNoRises]
    rfl
  exact prefixMask_oneRun_of_noRises
    (actualPrefixAbsorptionMask S a edges) hMaskNonempty hMaskNoRises

/-- The ORDINARY compressed cycle's q vertices and the ACTUAL
number p of maximal absorbed runs satisfy q+p≤2|S|.
No independent geometric hypothesis q/p is added. -/
theorem actualPrefixCompression_exposed_ordinary_bound
    (S : Set ℝ) (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {a d : ℝ} (ha : a ∈ S) (hd : d ∈ S)
    (had : a < d) (edges : List ℝ)
    (hEdges : ∀ e ∈ edges, e ∈ S)
    (hBad : edges.foldl (distanceSum S) a < d) :
    (risingPrefixEdges S a edges).length + 2 +
      prefixPlateauRunCount false (actualPrefixAbsorptionMask S a edges) ≤
      2 * hfin.toFinset.card := by
  have hCount :=
    risingPrefixEdges_compressed_cycle_card
      S hfin hpos hS ha hd had edges hEdges hBad
  have hRuns :=
    actualPrefixAbsorptionMask_runCount S a edges
  omega

/-- Uniform CORRECTED q=max(3,k+2) and ACTUAL p bound,
including the exceptional triangle and the case with no
absorbed runs. No proper-jump premise is necessary. -/
theorem actualPrefixCompression_exposed_corrected_bound
    (S : Set ℝ) (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {a d : ℝ} (ha : a ∈ S) (hd : d ∈ S)
    (had : a < d) (edges : List ℝ)
    (hEdges : ∀ e ∈ edges, e ∈ S)
    (hBad : edges.foldl (distanceSum S) a < d) :
    max 3 ((risingPrefixEdges S a edges).length + 2) +
      prefixPlateauRunCount false (actualPrefixAbsorptionMask S a edges) ≤
      2 * hfin.toFinset.card := by
  have hCount :=
    risingPrefixEdges_compressed_cycle_card
      S hfin hpos hS ha hd had edges hEdges hBad
  have hRuns :=
    actualPrefixAbsorptionMask_runCount S a edges
  omega

end AllThoseRamseyClasses.Applications.MetricSaturation
