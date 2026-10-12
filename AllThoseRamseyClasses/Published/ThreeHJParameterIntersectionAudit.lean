import PartiteConstruction.HalesJewett.Finite
import Mathlib.Tactic

/-!
# Three genuine Hales--Jewett lines: pairwise parameters, no common parameter

The remaining 2019 Lemma 2.30 rank increment has to handle a finite
family of generator-active native Hales--Jewett lines. A tempting,
but FALSE, simplification is:

  "If there is no coordinate variable on ALL selected lines,
   then TWO of the lines have disjoint sets of variable coordinates."

Even a family of THREE genuine length-3 Hales--Jewett lines refutes
this: take parameter sets {1,2}, {0,2}, {0,1}. Each pair shares a
variable coordinate, but the three lines have none in common.

These actual Line objects use an alphabet with one element
(PUnit) and a constant at the line's own excluded coordinate.
The phenomenon is purely combinatorial, so it persists with larger
nonempty alphabets and genuine nontrivial Ramsey systems.

This does NOT contradict the checked native common-coordinate
completion theorem; that theorem requires a coordinate common to
ALL generator-active lines of the tested structure.

It prevents reducing the unresolved maximal-rank multi-line
case merely to a PAIR of transverse lines. The proper history
argument must handle higher-order parameter intersections, without
an unjustified global-coordinate or pairwise-disjointness claim.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey.HalesJewett
open SuccessorTree

/-- For each i among three coordinate positions, choose the genuine
line which is CONSTANT exactly at i and parameter everywhere else. -/
def tripleOverlappingHJLines : Fin 3 → Line PUnit 3 :=
  fun i => {
    symbol := fun k =>
      if k = i then .const PUnit.unit else .parameter
    hasParameter := by
      by_cases hi : i = 0
      · refine ⟨1, ?_⟩
        simp [hi]
      · have h0 : (0 : Fin 3) ≠ i := Ne.symm hi
        exact ⟨0, by simp [h0]⟩
  }

/-- Each PAIR of distinct lines has a parameter coordinate in common. -/
theorem tripleOverlappingHJLines_pairwise_common :
    ∀ i j : Fin 3, i ≠ j →
      ∃ k : Fin 3,
        (tripleOverlappingHJLines i).symbol k = .parameter ∧
        (tripleOverlappingHJLines j).symbol k = .parameter := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact (hij rfl).elim
    | exact ⟨0, by simp [tripleOverlappingHJLines]⟩
    | exact ⟨1, by simp [tripleOverlappingHJLines]⟩
    | exact ⟨2, by simp [tripleOverlappingHJLines]⟩

/-- Nonetheless, the family of all THREE genuine lines has no
single coordinate variable on every one of them. -/
theorem tripleOverlappingHJLines_no_global_common :
    ¬ ∃ k : Fin 3,
        ∀ i : Fin 3,
          (tripleOverlappingHJLines i).symbol k = .parameter := by
  rintro ⟨k, hk⟩
  have hBad := hk k
  simp [tripleOverlappingHJLines] at hBad

/-- Therefore the implication from no global variable to the
existence of a parameter-disjoint pair is FALSE even for genuine
Hales--Jewett lines of length three. -/
theorem no_global_parameter_does_not_imply_disjoint_pair :
    ¬ ((¬ ∃ k : Fin 3,
             ∀ i : Fin 3,
               (tripleOverlappingHJLines i).symbol k = .parameter) →
         ∃ i j : Fin 3, i ≠ j ∧
           ∀ k : Fin 3,
             (tripleOverlappingHJLines i).symbol k ≠ .parameter ∨
             (tripleOverlappingHJLines j).symbol k ≠ .parameter) := by
  intro h
  obtain ⟨i, j, hij, hDisjoint⟩ :=
    h tripleOverlappingHJLines_no_global_common
  obtain ⟨k, hik, hjk⟩ :=
    tripleOverlappingHJLines_pairwise_common i j hij
  rcases hDisjoint k with hi | hj
  · exact hi hik
  · exact hj hjk

end AllThoseRamseyClasses.Published
