import AllThoseRamseyClasses.Applications.MetricFourPointCutoffArithmetic
import Mathlib.Tactic

/-!
# The repaired three-vertex cycle bound does not numerically exceed the printed cutoff

The literal universal |S|-vertex compression claim in the 2019
metric application was disproved for S={1,3}. The suggested
local statement change is to max(3,|S|). This raises a
numerical concern for the subsequent published local cutoff

    n = 2 |S| (|J_S|+1).

For any finite distance set containing a GENUINE proper jump,
|S|>=2, so max(3,|S|) <= 2|S|. Consequently the new
cycle-vertex bound, multiplied by the at-most-(|J|+1)
per-vertex closure factor, STILL fits the original n.

This is ONLY numerical compatibility. It does not establish
the corrected general path-compression and path-replacement
lemma, nor that closures of the compressed support have the
claimed size under the original U-closed weak test premises.
The finite S-metric Ramsey conclusion and the exact printed
local-completion argument therefore remain unverified.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- A proper jump requires at least two S-distances.
Hence the candidate corrected compression bound
max(3,|S|) cannot exceed twice the number of distances. -/
theorem metricCorrectedCycleBound_le_two_card_of_jump
    (S : Set ℝ) (hfin : S.Finite)
    {j : ℝ} (hj : Jump S j) :
    max 3 hfin.toFinset.card ≤ 2 * hfin.toFinset.card := by
  have hTwo : 2 ≤ hfin.toFinset.card :=
    metricFiniteS_card_two_of_proper_jump hfin hj
  omega

/-- Multiplying the corrected compressed-cycle vertex bound
by a per-source-vertex closure factor (|J|+1) is still
NUMERICALLY below the published candidate cutoff. -/
theorem metricCorrectedCycleBound_fits_printed_cutoff_of_jump
    (S : Set ℝ) (hfin : S.Finite)
    {j : ℝ} (hj : Jump S j) :
    max 3 hfin.toFinset.card *
      ((finiteJumpThresholdList S hfin).length + 1) ≤
      metricPrintedLocalCutoff S hfin := by
  have hcard : max 3 hfin.toFinset.card ≤
      2 * hfin.toFinset.card :=
    metricCorrectedCycleBound_le_two_card_of_jump S hfin hj
  unfold metricPrintedLocalCutoff
  exact Nat.mul_le_mul_right
    ((finiteJumpThresholdList S hfin).length + 1) hcard

end AllThoseRamseyClasses.Applications.MetricSaturation
