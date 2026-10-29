import AllThoseRamseyClasses.Applications.MetricBlockPathAbsorption
import AllThoseRamseyClasses.Applications.MetricPlateauProperJump
import AllThoseRamseyClasses.Applications.MetricFiniteWellDefined

/-!
# The literal block-bounded replacement clause for an unimportant S-path

This module combines the separately kernel-checked ingredients #709/#710.
The original edge list is an "unimportant path" in precisely the sense
that folding it from its already attained rounded prefix a does not
increase that prefix. The positive closing edge d is strictly longer
than a. The actual paper block B contains (at least) a longest edge
of the original path. To avoid a needless max choice, we only require
that B contains SOME edge of the original path. All distances in B
then lie below the same absorbed proper jump, by the proved finite
no-jump block decomposition.

A replacement P' ≼_S P means EACH replacement edge has an allowed
positive S-distance bounded above by SOME member of B, with no bound
on the replacement's number of edges. The theorem preserves the
rounded prefix and the strict closing-edge obstruction for EVERY
such replacement. The quantified replacement list is arbitrary;
it need not satisfy an independently assumed metric property.

The general construction of disjoint unimportant paths in a
non-S-metric cycle and the corrected quotient bound are DIFFERENT
remaining lemmas. This file does not claim the completed printed
`lem:Sequivalence`, the exact weak local completion or Ramsey.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Exact algebraic arbitrary replacement claim from the printed
cycle-compression proof. The original plateau and one actual edge
in the named no-jump paper block are source premises, not inferred
from a previously constructed compressed cycle.

For every replacement path P' whose edges are bounded by members
of that block, we construct a proper jump j that absorbs ALL
replacement edges, and preserve the bad closing edge d. -/
theorem metricUnimportantPaperBlock_replacement
    {S B : Set ℝ}
    (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S) (h4 : FourValues S)
    (hBlock : PaperBlock S B)
    {a d : ℝ} (ha : a ∈ S) (hd : d ∈ S)
    (had : a < d)
    (original replacement : List ℝ)
    (hOriginal : ∀ e ∈ original, e ∈ S)
    (hPlateau : original.foldl (distanceSum S) a = a)
    (hBlockWitness : ∃ b ∈ original, b ∈ B)
    (hReplace : ∀ e ∈ replacement,
      e ∈ S ∧ ∃ t ∈ B, e ≤ t) :
    ∃ j : ℝ, Jump S j ∧
      (∀ t ∈ B, t ≤ j) ∧
      distanceSum S a j = a ∧
      replacement.foldl (distanceSum S) a = a ∧
      replacement.foldl (distanceSum S) a < d := by
  obtain ⟨b, hbOrig, hbBlock⟩ := hBlockWitness
  have hbAbs : distanceSum S a b = a :=
    roundedFoldl_plateau_absorbs_each_edge
      hpos hS ha original hOriginal hPlateau b hbOrig
  obtain ⟨j, hjump, hBlockBound, _hja, hAbsJ⟩ :=
    roundedPlateau_paperBlock_bound_absorbed
      hfin hpos hS (associativeOn_of_fourValues hpos hS h4)
      hBlock ha hd had hbBlock hbAbs
  have hReplacementBound :
      ∀ e ∈ replacement, e ∈ S ∧ e ≤ j := by
    intro e he
    obtain ⟨heS, t, htBlock, het⟩ := hReplace e he
    exact ⟨heS, het.trans (hBlockBound t htBlock)⟩
  have hReplacementFold :
      replacement.foldl (distanceSum S) a = a :=
    roundedFoldl_eq_of_absorbed_bound
      hpos ha hAbsJ replacement hReplacementBound
  refine ⟨j, hjump, hBlockBound, hAbsJ, hReplacementFold, ?_⟩
  rw [hReplacementFold]
  exact had

/-- Exact finite-four-values specialization: well-definedness of
the rounded S-sum is DERIVED from finiteness and positivity,
rather than added as an extra manuscript hypothesis. -/
theorem metricUnimportantPaperBlock_replacement_finite
    {S B : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S) (h4 : FourValues S)
    (hBlock : PaperBlock S B)
    {a d : ℝ} (ha : a ∈ S) (hd : d ∈ S) (had : a < d)
    (original replacement : List ℝ)
    (hOriginal : ∀ e ∈ original, e ∈ S)
    (hPlateau : original.foldl (distanceSum S) a = a)
    (hBlockWitness : ∃ b ∈ original, b ∈ B)
    (hReplace : ∀ e ∈ replacement,
      e ∈ S ∧ ∃ t ∈ B, e ≤ t) :
    replacement.foldl (distanceSum S) a = a ∧
      replacement.foldl (distanceSum S) a < d := by
  obtain ⟨_, _, _, _, hFold, hBad⟩ :=
    metricUnimportantPaperBlock_replacement
      hfin hpos (wellDefined_of_finite hfin hpos) h4
      hBlock ha hd had original replacement
      hOriginal hPlateau hBlockWitness hReplace
  exact ⟨hFold, hBad⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
