import PartiteConstruction.HalesJewett.Finite
import Mathlib.Tactic

/-!
# Minimal non-common-parameter Hales--Jewett histories

The unsolved strict U-rank increase in repaired 2019 Lemma 2.30
cannot reduce a failed global common-variable-coordinate condition
to TWO parameter-disjoint lines. Three lines can have pairwise
overlapping parameter sets but empty triple intersection.

A CORRECT FINITE reduction is to choose a smallest subfamily J
whose variable sets have empty intersection. Then deleting ANY
one active line i from J restores a common parameter coordinate k_i
for ALL remaining lines, and i itself is CONSTANT at that coordinate.

This theorem is valid for an arbitrary finite selected family of
genuine Hales--Jewett lines in the native picture. No global Fintype
for the line index I is required; S : Finset I is already finite.

The conclusion is only finite-combinatorial history geometry.
Applying retractions to the rest of a split and constructing a
proper U-closed K-boundary with absolute projected rank-j budgets
are still separate, open tasks. No higher-rank Ramsey theorem is
asserted here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey.HalesJewett

universe u v
variable {I : Type v} {N : ℕ}

/-- A coordinate which is variable for every member of a selected
finite line index family. No partite carrier or closure hull is involved. -/
def HasCommonSelectedCoordinate
    (variableAt : I → Fin N → Prop) (S : Finset I) : Prop :=
  ∃ k : Fin N, ∀ i ∈ S, variableAt i k

/-- Given finitely many lines with no shared variable coordinate,
choose a MINIMAL obstruction. On removing any one of its lines,
the rest share a coordinate which is constant on the removed line.

This is the correct replacement for the false pairwise-disjoint
conclusion sometimes inferred from failure of a global coordinate. -/
theorem exists_minimal_noncommon_subfamily
    (variableAt : I → Fin N → Prop)
    (S : Finset I)
    (hBad : ¬ HasCommonSelectedCoordinate variableAt S) :
    ∃ T : Finset I,
      T ⊆ S ∧
      ¬ HasCommonSelectedCoordinate variableAt T ∧
      (∀ i ∈ T, ∃ k : Fin N,
        ¬ variableAt i k ∧
        ∀ j ∈ T.erase i, variableAt j k) := by
  classical
  let eligible (n : ℕ) : Prop :=
    ∃ T : Finset I, T ⊆ S ∧ T.card = n ∧
      ¬ HasCommonSelectedCoordinate variableAt T
  have hExists : ∃ n : ℕ, eligible n :=
    ⟨S.card, S, Finset.Subset.rfl, rfl, hBad⟩
  let n : ℕ := Nat.find hExists
  obtain ⟨T, hSub, hCard, hTBad⟩ :
      eligible n := Nat.find_spec hExists
  refine ⟨T, hSub, hTBad, ?_⟩
  intro i hi
  have hEraseGood :
      HasCommonSelectedCoordinate variableAt (T.erase i) := by
    by_contra hEraseBad
    have hEraseSub : T.erase i ⊆ S := by
      intro j hj
      exact hSub ((Finset.mem_erase.mp hj).2)
    have hShort : eligible (T.erase i).card :=
      ⟨T.erase i, hEraseSub, rfl, hEraseBad⟩
    have hMin : n ≤ (T.erase i).card :=
      Nat.find_min' hExists hShort
    have hPos : 0 < T.card :=
      Finset.card_pos.mpr ⟨i, hi⟩
    have hEraseCard : (T.erase i).card = T.card - 1 :=
      Finset.card_erase_of_mem hi
    omega
  obtain ⟨k, hEvery⟩ := hEraseGood
  refine ⟨k, ?_, hEvery⟩
  intro hiVariable
  apply hTBad
  refine ⟨k, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact hiVariable
  · exact hEvery j (Finset.mem_erase.mpr ⟨hji, hj⟩)

/-- The reduction instantiated with the ACTUAL parameter
coordinates of genuine native Hales--Jewett line objects. -/
theorem exists_minimal_noncommon_HJ_lines
    {Alphabet : Type u}
    (lines : I → Line Alphabet N)
    (S : Finset I)
    (hBad : ¬ ∃ k : Fin N,
      ∀ i ∈ S, (lines i).symbol k = .parameter) :
    ∃ T : Finset I, T ⊆ S ∧
      (¬ ∃ k : Fin N,
        ∀ i ∈ T, (lines i).symbol k = .parameter) ∧
      (∀ i ∈ T, ∃ k : Fin N,
        (lines i).symbol k ≠ .parameter ∧
        ∀ j ∈ T.erase i, (lines j).symbol k = .parameter) := by
  exact exists_minimal_noncommon_subfamily
    (fun i k => (lines i).symbol k = .parameter) S hBad

end AllThoseRamseyClasses.Published
