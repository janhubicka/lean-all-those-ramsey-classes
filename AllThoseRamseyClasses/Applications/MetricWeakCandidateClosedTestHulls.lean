import AllThoseRamseyClasses.Applications.MetricWeakCandidateFiniteHulls
import AllThoseRamseyClasses.Applications.MetricCompositionClosedSubsetTests
import Mathlib.Tactic

/-!
# From genuine closed local tests to small candidate function-closed hulls

The two-step composition identity is verified in VALID functional
S-metrics, and a specified exactly function-closed local completion
transfers it to the original WEAK source. Separately, the source
composition identity implies the finite F_j-closed hull of any
finite seed list has at most (number of seeds)(|J|+1) vertices.

These theorems combine those two components *without* a circular
assumption: the existence of exact closed-subset completions for
every relevant two-step source pattern is an EXPLICIT premise.
No closed subset is assumed to be small in that premise.

The output provides a small closed hull AFTER the source
composition identity has been obtained. This does not itself
derive the local completion premise from the manuscript's
bounded U-closed weak induced-substructure tests.

For a four-point source support and at least two allowed
distances, the resulting conditional size bound is at most
2|S|(|J|+1). This is numerical compatibility with the printed
cutoff, NOT a validation of its original proof or cycle lemma.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Explicit source local COMPLETION TESTS for every defined
two-step pattern imply a bounded F_j-closed hull for an
arbitrary finite list of original vertices. There is no
metric assumed on the weak candidate itself. -/
theorem metricCandidateFiniteHull_of_closedLocalTests
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (J : Finset ℝ)
    (hJump : ∀ j ∈ J, Jump S j)
    (hLocal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        fA j x = some y → fA k y = some z →
          MetricFourPointCompositionClosedSubsetCompletion
            S fA j k x y z)
    (seeds : List A) :
    ∃ C : Finset A,
      (∀ x ∈ seeds, x ∈ C) ∧
      C.card ≤ seeds.length * (J.card + 1) ∧
      MetricCandidateFinsetClosed J fA C := by
  have hNormalSet :=
    metricCandidateComposition_normalform_of_closedSubsetTests
      hpos fA (↑J : Set ℝ) hJump hLocal
  have hNormal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A, fA j x = some y →
        fA k y = some z → fA k x = some z := by
    intro j hj k hk x y z hxy hyz
    exact (hNormalSet j hj k hk x y z hxy hyz).2
  exact metricCandidateFiniteHull_list_exists
    J fA hNormal seeds

/-- Four source vertices have a joint FUNCTION-CLOSED local
support of size at most 4(|J|+1), provided the original
candidate itself passes the explicitly stated exact
closed-subset composition tests. -/
theorem metricCandidateFourPointHull_of_closedLocalTests
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (J : Finset ℝ)
    (hJump : ∀ j ∈ J, Jump S j)
    (hLocal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        fA j x = some y → fA k y = some z →
          MetricFourPointCompositionClosedSubsetCompletion
            S fA j k x y z)
    (a b c d : A) :
    ∃ C : Finset A,
      a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
      C.card ≤ 4 * (J.card + 1) ∧
      MetricCandidateFinsetClosed J fA C := by
  obtain ⟨C, hCover, hBound, hClosed⟩ :=
    metricCandidateFiniteHull_of_closedLocalTests
      hpos fA J hJump hLocal [a, b, c, d]
  refine ⟨C, hCover a (by simp),
    hCover b (by simp), hCover c (by simp),
    hCover d (by simp), ?_, hClosed⟩
  simpa using hBound

/-- If the allowed finite distance set contains at least two
distances, the conditional four-seed hull also fits numerically
inside the manuscript's proposed 2|S|(|J|+1) cutoff. This
does NOT imply the source local-completion hypotheses already
guarantee the required local tests; that bridge is still open. -/
theorem metricCandidateFourPointHull_fits_printed_bound_of_closedTests
    (S J : Finset ℝ)
    (hSCard : 2 ≤ S.card)
    (hpos : Positive (↑S : Set ℝ))
    {A : Type u}
    (fA : ℝ → A → Option A)
    (hJump : ∀ j ∈ J, Jump (↑S : Set ℝ) j)
    (hLocal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        fA j x = some y → fA k y = some z →
          MetricFourPointCompositionClosedSubsetCompletion
            (↑S : Set ℝ) fA j k x y z)
    (a b c d : A) :
    ∃ C : Finset A,
      a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
      C.card ≤ 2 * S.card * (J.card + 1) ∧
      MetricCandidateFinsetClosed J fA C := by
  obtain ⟨C, ha, hb, hc, hd, hBound, hClosed⟩ :=
    metricCandidateFourPointHull_of_closedLocalTests
      hpos fA J hJump hLocal a b c d
  refine ⟨C, ha, hb, hc, hd, ?_, hClosed⟩
  have hMul : 4 * (J.card + 1) ≤
      (2 * S.card) * (J.card + 1) :=
    Nat.mul_le_mul_right (J.card + 1) (by omega)
  exact hBound.trans hMul

end AllThoseRamseyClasses.Applications.MetricSaturation
