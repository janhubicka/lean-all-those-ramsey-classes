import AllThoseRamseyClasses.Applications.MetricConvexityTransfer
import Mathlib.Tactic

/-!
# Correct the TWO-input finite-distance quantifiers in the S-metric application

The printed proof of `prop:Smetric` chooses a finite distance set
containing only distances from B. A Ramsey arrow for A inside B
instead requires the same finite S' to contain distances of BOTH
finite input structures A and B (even when their distance sets
are disjoint).

Here the two input carriers may be of DIFFERENT types and may
carry different ordered S-metrics dA, dB. We construct ONE finite
four-values subset T of S containing BOTH finite distance supports.
More strongly, jump-threshold convexity is transferred exactly
from S to T for BOTH ordered metrics simultaneously.

The proof directly reuses `exists_finite_capped_extension`
and `jumpConvex_iff_of_capped_closed`. The generating set
includes both input supports and, if necessary, one ambient
distance so there is a cap. S empty is treated separately;
then all jump convexity conditions are vacuous.

This is source-faithful to the reduction's needed A/B quantifiers.
It is NOT the complete infinite-S Ramsey theorem: equivalence
of the manuscript's literal infinite-S maximal-block convexity
with jump-threshold convexity and the finite-S Ramsey arrow
remain separate obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- One common finite four-values distance set for TWO ordered
S-metric inputs, preserving jump convexity on both original
carriers. Finite distance supports may be empty. -/
theorem finiteFourValues_twoInput_jumpConvex_transfer
    {S DA DB : Set ℝ}
    {VA : Type u} {VB : Type v}
    [LinearOrder VA] [LinearOrder VB]
    (dA : VA → VA → ℝ) (dB : VB → VB → ℝ)
    (hpos : Positive S) (hS : WellDefined S)
    (h4 : FourValues S)
    (hDA : DA.Finite) (hDB : DB.Finite)
    (hDAS : DA ⊆ S) (hDBS : DB ⊆ S)
    (hdiagA : ∀ x, dA x x = 0)
    (hdiagB : ∀ x, dB x x = 0)
    (hrangeA : ∀ x y, x ≠ y → dA x y ∈ DA)
    (hrangeB : ∀ x y, x ≠ y → dB x y ∈ DB) :
    ∃ T : Set ℝ,
      T.Finite ∧ DA ⊆ T ∧ DB ⊆ T ∧ T ⊆ S ∧
      WellDefined T ∧ FourValues T ∧
      (JumpConvex S dA ↔ JumpConvex T dA) ∧
      (JumpConvex S dB ↔ JumpConvex T dB) := by
  classical
  by_cases hSne : S.Nonempty
  · obtain ⟨s, hs⟩ := hSne
    let D : Set ℝ := insert s (DA ∪ DB)
    have hDfin : D.Finite := (hDA.union hDB).insert s
    have hDS : D ⊆ S := by
      intro t ht
      rcases (Set.mem_insert_iff.mp ht) with rfl | ht
      · exact hs
      · rcases ht with ha | hb
        · exact hDAS ha
        · exact hDBS hb
    let F : Finset ℝ := hDfin.toFinset
    have hF : F.Nonempty :=
      ⟨s, hDfin.mem_toFinset.mpr (by simp [D])⟩
    let m : ℝ := F.max' hF
    have hmD : m ∈ D :=
      hDfin.mem_toFinset.mp (Finset.max'_mem F hF)
    have hDm : ∀ t ∈ D, t ≤ m := by
      intro t ht
      exact Finset.le_max' F t (hDfin.mem_toFinset.mpr ht)
    obtain ⟨T, hTfin, hDT, hTS, hBound, hClosed, hTwell, hTassoc⟩ :=
      exists_finite_capped_extension hpos hS
        (associativeOn_of_fourValues hpos hS h4)
        (hDS hmD) hDfin hDS hDm
    have hmT : m ∈ T := hDT hmD
    have hTA : DA ⊆ T := by
      intro t ht
      apply hDT
      exact Set.mem_insert_of_mem s (Or.inl ht)
    have hTB : DB ⊆ T := by
      intro t ht
      apply hDT
      exact Set.mem_insert_of_mem s (Or.inr ht)
    have hTpos : Positive T := by
      intro t ht
      exact hpos t (hTS ht)
    have hTfour : FourValues T :=
      fourValues_of_associativeOn hTpos hTwell hTassoc
    have hConvA : JumpConvex S dA ↔ JumpConvex T dA :=
      jumpConvex_iff_of_capped_closed dA hpos hTfin hTS
        hmT hBound hClosed hdiagA
        (fun x y hxy => hTA (hrangeA x y hxy))
    have hConvB : JumpConvex S dB ↔ JumpConvex T dB :=
      jumpConvex_iff_of_capped_closed dB hpos hTfin hTS
        hmT hBound hClosed hdiagB
        (fun x y hxy => hTB (hrangeB x y hxy))
    exact ⟨T, hTfin, hTA, hTB, hTS, hTwell, hTfour, hConvA, hConvB⟩
  · have hSEmpty : S = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hSne
    have hDAEmpty : DA ⊆ (∅ : Set ℝ) := by
      intro t ht
      have hmem := hDAS ht
      simpa [hSEmpty] using hmem
    have hDBEmpty : DB ⊆ (∅ : Set ℝ) := by
      intro t ht
      have hmem := hDBS ht
      simpa [hSEmpty] using hmem
    have hConvS_A : JumpConvex S dA := by
      intro j hj
      exact False.elim (by simpa [hSEmpty] using hj.1)
    have hConvS_B : JumpConvex S dB := by
      intro j hj
      exact False.elim (by simpa [hSEmpty] using hj.1)
    have hConvEmpty_A : JumpConvex (∅ : Set ℝ) dA := by
      intro j hj
      exact False.elim hj.1
    have hConvEmpty_B : JumpConvex (∅ : Set ℝ) dB := by
      intro j hj
      exact False.elim hj.1
    refine ⟨∅, Set.finite_empty, hDAEmpty, hDBEmpty,
      Set.empty_subset S, ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact False.elim ha
    · intro a ha
      exact False.elim ha
    · exact ⟨fun _ => hConvEmpty_A, fun _ => hConvS_A⟩
    · exact ⟨fun _ => hConvEmpty_B, fun _ => hConvS_B⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
