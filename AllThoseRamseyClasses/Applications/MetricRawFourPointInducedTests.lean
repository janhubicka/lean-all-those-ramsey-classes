import AllThoseRamseyClasses.Applications.MetricLocalCompositionTests
import AllThoseRamseyClasses.Applications.MetricWeakCandidateFiniteHulls
import Mathlib.Tactic

/-!
# Raw four-vertex induced-function tests, without assuming a closed hull

The printed metric Ramsey proof needs to transfer the valid-target
two-step F_j composition law back to an arbitrary weak candidate,
then use that law to bound the candidate's function-closed hulls.

Assuming a SMALL closed candidate hull before deriving composition
is circular. Here is an independent, conditional alternative:
take the four ORIGINAL support vertices {x,y,z,rep_k(x)} and
RESTRICT each Option-valued function to values whose endpoints
both belong to that support. This induced partial function is
defined even if the support is not closed under the source maps.

If this raw induced support has an exact Option-preserving
local completion into a valid metric-functional target, it
forces the two-step composition law on the original weak source.
A direct application of the already proved finite-hull theorem
then gives closed hulls of at most m (|J|+1) vertices for m seeds.

The support genuinely contains at most FOUR vertices. It is not
assumed function-closed and the theorem never invokes a small
closed hull to justify its own local completion.

IMPORTANT SOURCE-PROOF DISTINCTION: the required completion
preserves the induced Option values INCLUDING UNDEFINEDNESS.
It has NOT been shown that the 2019 paper's weak U-closed
induced-substructure hypothesis supplies this exact raw test.
In particular, for functions whose values lie outside the
support, the induced function is undefined. If the manuscript
permits local completions to enlarge such domains, the
hypothesis here is strictly stronger. No printed Ramsey
conclusion follows without that source-matching proof.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Keep an old partial-function value exactly when its
endpoint lies in P. A defined value outside P becomes
undefined. No closure of P is assumed. -/
noncomputable def metricCandidateRawRestrictedValue
    {A : Type u}
    (P : Finset A) (fA : ℝ → A → Option A)
    (j : ℝ) (x : A) : Option A := by
  classical
  exact (fA j x).bind (fun y => if y ∈ P then some y else none)

/-- Values whose endpoint is in P survive raw restriction. -/
theorem metricCandidateRawRestrictedValue_of_some_mem
    {A : Type u}
    (P : Finset A) (fA : ℝ → A → Option A)
    (j : ℝ) (x y : A)
    (hxy : fA j x = some y) (hy : y ∈ P) :
    metricCandidateRawRestrictedValue P fA j x = some y := by
  classical
  simp [metricCandidateRawRestrictedValue, hxy, hy]

/-- Undefinedness is retained exactly by raw restriction. -/
theorem metricCandidateRawRestrictedValue_of_none
    {A : Type u}
    (P : Finset A) (fA : ℝ → A → Option A)
    (j : ℝ) (x : A)
    (hx : fA j x = none) :
    metricCandidateRawRestrictedValue P fA j x = none := by
  classical
  simp [metricCandidateRawRestrictedValue, hx]

/-- If the designated value-or-self of x lies inside P,
the raw restriction at x equals its FULL original value,
whether that value was defined or undefined. -/
theorem metricCandidateRawRestrictedValue_of_rep_mem
    {A : Type u}
    (P : Finset A) (fA : ℝ → A → Option A)
    (j : ℝ) (x : A)
    (hrep : metricClosureRepresentative (fA j) x ∈ P) :
    metricCandidateRawRestrictedValue P fA j x = fA j x := by
  classical
  cases hx : fA j x with
  | none =>
      simp [metricCandidateRawRestrictedValue, hx]
  | some y =>
      have hy : y ∈ P := by
        simpa [metricClosureRepresentative, hx] using hrep
      simp [metricCandidateRawRestrictedValue, hx, hy]

/-- The four ORIGINAL vertices sufficient to test a defined
two-step composition F_k(F_j(x)) under a raw Option restriction. -/
noncomputable def metricCandidateFourPointRawSupport
    {A : Type u} (fA : ℝ → A → Option A)
    (k : ℝ) (x y z : A) : Finset A := by
  classical
  exact {x, y, z, metricClosureRepresentative (fA k) x}

/-- Support cardinality is at most four, independently of
the size of the eventual source function-closed hull. -/
theorem metricCandidateFourPointRawSupport_card_le
    {A : Type u} (fA : ℝ → A → Option A)
    (k : ℝ) (x y z : A) :
    (metricCandidateFourPointRawSupport fA k x y z).card ≤ 4 := by
  classical
  unfold metricCandidateFourPointRawSupport
  exact Finset.card_le_four

/-- A locally completed raw support with exact Option data.
An extension map is required to be injective ONLY on P;
it may be arbitrary outside P.

This is an EXPLICIT completion premise, not the assertion
that all weak candidate subsets have such completions. -/
def MetricCandidateRawInducedCompletion
    (S : Set ℝ)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (P : Finset A) : Prop :=
  ∃ (V : Type u) (o : LinearOrder V)
    (dV : V → V → ℝ)
    (fV : ℝ → V → Option V)
    (i : A → V),
    MetricOn S dV ∧
    (∀ t : ℝ, Jump S t →
      @MetricJumpClosureLaw V o dV (fV t) t) ∧
    Set.InjOn i (↑P : Set A) ∧
    (∀ t : ℝ, ∀ x : A, x ∈ P →
      fV t (i x) =
        Option.map i (metricCandidateRawRestrictedValue P fA t x))

/-- A precise four-point RAW induced completion supplies the
four-point local test used by the already verified
source normal-form transfer theorem. No function-closed
hull is introduced in this implication. -/
theorem metricFourPointCompositionLocalTest_of_rawInducedCompletion
    {S : Set ℝ}
    {A : Type u}
    (fA : ℝ → A → Option A)
    (j k : ℝ) (x y z : A)
    (hjx : fA j x = some y)
    (hky : fA k y = some z)
    (hRaw : MetricCandidateRawInducedCompletion S fA
      (metricCandidateFourPointRawSupport fA k x y z)) :
    MetricFourPointCompositionLocalTest S fA j k x y z := by
  classical
  let P : Finset A := metricCandidateFourPointRawSupport fA k x y z
  obtain ⟨V, o, dV, fV, i, hdV, hLaw, hInj, hExact⟩ := hRaw
  have hP : (↑P : Set A) =
      ({x, y, z, metricClosureRepresentative (fA k) x} : Set A) := by
    ext a
    simp [P, metricCandidateFourPointRawSupport]
  have hx : x ∈ P := by
    simp [P, metricCandidateFourPointRawSupport]
  have hy : y ∈ P := by
    simp [P, metricCandidateFourPointRawSupport]
  have hz : z ∈ P := by
    simp [P, metricCandidateFourPointRawSupport]
  have hrep :
      metricClosureRepresentative (fA k) x ∈ P := by
    simp [P, metricCandidateFourPointRawSupport]
  have hJ : metricCandidateRawRestrictedValue P fA j x = fA j x := by
    rw [metricCandidateRawRestrictedValue_of_some_mem
      P fA j x y hjx hy, hjx]
  have hKY : metricCandidateRawRestrictedValue P fA k y = fA k y := by
    rw [metricCandidateRawRestrictedValue_of_some_mem
      P fA k y z hky hz, hky]
  have hKX : metricCandidateRawRestrictedValue P fA k x = fA k x :=
    metricCandidateRawRestrictedValue_of_rep_mem P fA k x hrep
  refine ⟨V, o, dV, fV, i, hdV, hLaw, ?_, ?_, ?_, ?_⟩
  · simpa [hP] using hInj
  · simpa [hJ] using hExact j x hx
  · simpa [hKY] using hExact k y hy
  · simpa [hKX] using hExact k x hx

/-- Under raw four-point Option-preserving local completions,
all defined two-step source compositions satisfy the valid
higher-jump normal form. In particular the candidate's
F_j-closed orbits are finite WITHOUT any prior hull assumption. -/
theorem metricCandidateComposition_normalform_of_rawInducedTests
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (J : Finset ℝ)
    (hJump : ∀ j ∈ J, Jump S j)
    (hRaw : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        fA j x = some y → fA k y = some z →
        MetricCandidateRawInducedCompletion S fA
          (metricCandidateFourPointRawSupport fA k x y z)) :
    ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : A,
      fA j x = some y → fA k y = some z →
      j < k ∧ fA k x = some z := by
  intro j hj k hk x y z hxy hyz
  have hLocal : MetricFourPointCompositionLocalTest S fA j k x y z :=
    metricFourPointCompositionLocalTest_of_rawInducedCompletion
      fA j k x y z hxy hyz (hRaw j hj k hk x y z hxy hyz)
  exact metricJumpComposition_normalform_of_localTest
    hpos fA j k (hJump j hj) (hJump k hk)
    x y z hxy hyz hLocal

/-- Exact raw-induced tests on each four-original-vertex
composition support produce a genuinely F_j-CLOSED hull of
any finite source seed list, without assuming a bounded
closed hull as a premise of the local tests. -/
theorem metricCandidateFiniteHull_of_rawInducedTests
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (J : Finset ℝ)
    (hJump : ∀ j ∈ J, Jump S j)
    (hRaw : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        fA j x = some y → fA k y = some z →
        MetricCandidateRawInducedCompletion S fA
          (metricCandidateFourPointRawSupport fA k x y z))
    (seeds : List A) :
    ∃ C : Finset A,
      (∀ x ∈ seeds, x ∈ C) ∧
      C.card ≤ seeds.length * (J.card + 1) ∧
      MetricCandidateFinsetClosed J fA C := by
  have hNormal :
      ∀ j ∈ J, ∀ k ∈ J,
        ∀ x y z : A,
          fA j x = some y → fA k y = some z →
          fA k x = some z := by
    intro j hj k hk x y z hxy hyz
    exact (metricCandidateComposition_normalform_of_rawInducedTests
      hpos fA J hJump hRaw j hj k hk x y z hxy hyz).2
  exact metricCandidateFiniteHull_list_exists J fA hNormal seeds

end AllThoseRamseyClasses.Applications.MetricSaturation
