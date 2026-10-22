import AllThoseRamseyClasses.Applications.MetricThresholdClassKeyNesting
import Mathlib.Data.Finset.Sort

/-!
# Enumerate exactly the proper jumps of one finite S-metric distance set

A finite subset S of positive real distances has finitely many
proper jump thresholds. Here we provide the exact finite list
in STRICTLY INCREASING order, with an iff membership theorem.
It is therefore already suitable for the separately verified
threshold-key nesting and all-level convex-order refinements.

Only S.Finite is required for this enumeration. The algebraic
four-values and rounding hypotheses enter when the actual
metric class-key functions are constructed, not here.

This does not yet assert convex amalgamation, compatibility
of partial closure functions, or the published exact weak
local-completion statement.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The finite list of all proper jump thresholds, from smallest
to largest, with no duplicates. The choice uses only the finite
set S; all jump predicates have their original 2019 meaning. -/
noncomputable def finiteJumpThresholdList
    (S : Set ℝ) (hfinite : S.Finite) : List ℝ := by
  classical
  exact ((hfinite.toFinset).filter (Jump S)).sort

/-- The list contains precisely the proper jumps of S, not
merely an arbitrary set of idempotent values. -/
theorem mem_finiteJumpThresholdList_iff
    (S : Set ℝ) (hfinite : S.Finite) (j : ℝ) :
    j ∈ finiteJumpThresholdList S hfinite ↔ Jump S j := by
  classical
  change j ∈ ((hfinite.toFinset).filter (Jump S)).sort ↔ _
  rw [Finset.mem_sort (· ≤ ·)]
  simp only [Finset.mem_filter, hfinite.mem_toFinset]
  exact ⟨And.right, fun hj => ⟨hj.1, hj⟩⟩

/-- Strictly increasing enumeration, so the corresponding
j-equivalence classes run from finer to coarser. -/
theorem finiteJumpThresholdList_pairwise
    (S : Set ℝ) (hfinite : S.Finite) :
    (finiteJumpThresholdList S hfinite).Pairwise (· < ·) := by
  classical
  change (((hfinite.toFinset).filter (Jump S)).sort).Pairwise (· < ·)
  exact (Finset.sortedLT_sort _).pairwise

/-- The precise pair of hypotheses used for the finite
nested-class construction. -/
theorem finiteJumpThresholdList_certificate
    (S : Set ℝ) (hfinite : S.Finite) :
    ∃ (levels : List ℝ),
      levels.Pairwise (· < ·) ∧
      ∀ j : ℝ, j ∈ levels ↔ Jump S j := by
  refine ⟨finiteJumpThresholdList S hfinite,
    finiteJumpThresholdList_pairwise S hfinite, ?_⟩
  intro j
  exact mem_finiteJumpThresholdList_iff S hfinite j

end AllThoseRamseyClasses.Applications.MetricSaturation
