import AllThoseRamseyClasses.Applications.MetricFourValues

/-!
# Well-defined rounded sums on finite positive distance sets

The paper's finite-S applications assume four-values but do not
separately assume well-definedness of the rounded sum, since it
is a maximum of finitely many candidates. We prove this assumption
is automatic for every finite positive distance set, without
using four-values. The empty S case is vacuous.

This makes the subsequent finite-block lemma literally match
the original published assumptions, rather than relying on an
independently assumed well-definedness condition.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- On a finite positive allowed distance set the actual supremum
is attained: the candidate set contains a and is finite. -/
theorem wellDefined_of_finite {S : Set ℝ}
    (hfin : S.Finite) (hpos : Positive S) :
    WellDefined S := by
  intro a ha b hb
  let C : Set ℝ := {s | s ∈ S ∧ s ≤ a + b}
  have hCfin : C.Finite := hfin.subset (fun s hs => hs.1)
  have haC : a ∈ C := ⟨ha, by linarith [hpos b hb]⟩
  have hCne : C.Nonempty := ⟨a, haC⟩
  let F : Finset ℝ := hCfin.toFinset
  have hF : F.Nonempty :=
    ⟨a, hCfin.mem_toFinset.mpr haC⟩
  let m : ℝ := F.max' hF
  have hmC : m ∈ C :=
    hCfin.mem_toFinset.mp (Finset.max'_mem F hF)
  have hmax : ∀ s ∈ C, s ≤ m := by
    intro s hs
    exact Finset.le_max' F s (hCfin.mem_toFinset.mpr hs)
  have hsum_le : distanceSum S a b ≤ m := by
    change sSup C ≤ m
    exact csSup_le hCne hmax
  have hm_le : m ≤ distanceSum S a b :=
    le_distanceSum_of_le_add hmC.1 hmC.2
  have heq : distanceSum S a b = m :=
    le_antisymm hsum_le hm_le
  rw [heq]
  exact hmC.1

end AllThoseRamseyClasses.Applications.MetricSaturation
