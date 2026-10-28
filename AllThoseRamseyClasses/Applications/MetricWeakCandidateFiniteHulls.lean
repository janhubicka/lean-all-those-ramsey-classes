import AllThoseRamseyClasses.Applications.MetricWeakCandidateDirectOrbit
import Mathlib.Tactic

/-!
# Small function-closed hulls for an arbitrary finite list of seeds

Suppose a WEAK candidate has Option-valued functions F_j which
satisfy the higher-jump two-step composition normal form for
every j in a finite level set J. This condition alone already
makes the F_j-generated closure of each seed equal to its
one-step direct orbit (the imported theorem).

Here we close a finite LIST of seeds by taking the union of
their individual finite closed orbits. Its size is bounded
by (#seeds) * (|J|+1), with no metric structure on the source
and no global completion target.

The four-seed case is tailored to the four original vertices
{x,y,z,rep_k(x)} in local F_j composition/coherence tests.
It gives a 4*(|J|+1) bound, but ONLY after the source normal
form has been justified. We do NOT derive that normal form
from the printed weak U-closed local tests, and this does
not certify the original 2|S|(|J_S|+1) cutoff on its own.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Closure of a finite source set under all selected partial
F_j maps, with undefined values ignored. -/
def MetricCandidateFinsetClosed
    {A : Type u}
    (J : Finset ℝ) (f : ℝ → A → Option A)
    (C : Finset A) : Prop :=
  ∀ j ∈ J, ∀ y ∈ C, ∀ z : A,
    f j y = some z → z ∈ C

/-- A finite UNION of two function-closed source subsets
is again function-closed; no additional amalgamation
property or metric assumption is needed. -/
theorem metricCandidateFinsetClosed_union
    {A : Type u} [DecidableEq A]
    (J : Finset ℝ) (f : ℝ → A → Option A)
    (C D : Finset A)
    (hC : MetricCandidateFinsetClosed J f C)
    (hD : MetricCandidateFinsetClosed J f D) :
    MetricCandidateFinsetClosed J f (C ∪ D) := by
  classical
  intro j hj y hy z hyz
  rcases Finset.mem_union.mp hy with hc | hd
  · exact Finset.mem_union.mpr
      (Or.inl (hC j hj y hc z hyz))
  · exact Finset.mem_union.mpr
      (Or.inr (hD j hj y hd z hyz))

/-- Every finite LIST of prescribed seeds in a weak candidate
has a genuine function-closed finite hull of cardinal at most
(#seeds)(|J|+1) whenever the two-step normal form holds. -/
theorem metricCandidateFiniteHull_list_exists
    {A : Type u}
    (J : Finset ℝ) (f : ℝ → A → Option A)
    (hNormal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        f j x = some y → f k y = some z →
        f k x = some z)
    (seeds : List A) :
    ∃ C : Finset A,
      (∀ x ∈ seeds, x ∈ C) ∧
      C.card ≤ seeds.length * (J.card + 1) ∧
      MetricCandidateFinsetClosed J f C := by
  classical
  induction seeds with
  | nil =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · intro x hx
        cases hx
      · simp
      · intro j hj y hy z hyz
        simp at hy
  | cons x xs ih =>
      obtain ⟨C, hCover, hBound, hClosed⟩ := ih
      obtain ⟨D, hx, hSingle, hDClosed⟩ :=
        metricCandidateFiniteOrbit_closed_small_of_normalform
          J f hNormal x
      refine ⟨D ∪ C, ?_, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with hxy | hrest
        · subst y
          exact Finset.mem_union.mpr (Or.inl hx)
        · exact Finset.mem_union.mpr
            (Or.inr (hCover y hrest))
      · calc
          (D ∪ C).card ≤ D.card + C.card :=
            Finset.card_union_le D C
          _ ≤ (J.card + 1) + xs.length * (J.card + 1) :=
            Nat.add_le_add hSingle hBound
          _ = (xs.length + 1) * (J.card + 1) := by
            simp only [add_mul, one_mul]
            omega
      · exact metricCandidateFinsetClosed_union
          J f D C hDClosed hClosed

/-- Four arbitrary source vertices, possibly overlapping, have
a joint function-closed hull of size at most 4(|J|+1)
UNDER the original candidate composition normal form. -/
theorem metricCandidateFiniteHull_four_exists
    {A : Type u}
    (J : Finset ℝ) (f : ℝ → A → Option A)
    (hNormal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        f j x = some y → f k y = some z →
        f k x = some z)
    (a b c d : A) :
    ∃ C : Finset A,
      a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
      C.card ≤ 4 * (J.card + 1) ∧
      MetricCandidateFinsetClosed J f C := by
  obtain ⟨C, hCover, hBound, hClosed⟩ :=
    metricCandidateFiniteHull_list_exists
      J f hNormal [a, b, c, d]
  refine ⟨C, hCover a (by simp),
    hCover b (by simp), hCover c (by simp),
    hCover d (by simp), ?_, hClosed⟩
  simpa using hBound

end AllThoseRamseyClasses.Applications.MetricSaturation
