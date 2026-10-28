import AllThoseRamseyClasses.Applications.MetricLocalCompositionTests

/-!
# Recover candidate F_j composition from exact closed-subset completions

The printed metric local-completion proof requires transfer of the
higher-jump composition law back from VALID target metrics to a
potentially weak original candidate.

A completion of a specified *function-closed* source subset C can
be tested on the four original points x, y, z and rep_k(x)
whenever F_j(x)=y and F_k(y)=z. The local map need only be
injective on those four points, not on the whole candidate.
All Option-valued functions on C must be preserved exactly,
including when undefined; each target may be different.

The first theorem constructs the appropriate four-point
local test by extending the map on C to an arbitrary total
map on A. The second transfers the necessary source
composition equation, and the third packages the condition
for all levels in a selected set J.

The key remaining SOURCE-PROOF GAP is whether the manuscript's
weak U-closed induced-substructure hypotheses supply such
function-closed C with a uniform size bound. These lemmas
do not assume that implication and do not claim the printed
weak local-completion cutoff is certified.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- An exact local completion of a source function-CLOSED subset
containing the four relevant original vertices. The target has
all proper-jump F_j laws and preserves every defined OR
undefined original function value on C.

Unlike a completion of an arbitrary weak induced subset,
this condition includes exact function closure of C. -/
def MetricFourPointCompositionClosedSubsetCompletion
    (S : Set ℝ) {A : Type u}
    (fA : ℝ → A → Option A)
    (j k : ℝ) (x y z : A) : Prop :=
  ∃ (C : Set A) (fC : ℝ → C → Option C)
    (V : Type u) (o : LinearOrder V)
    (dV : V → V → ℝ)
    (fV : ℝ → V → Option V) (e : C → V),
    ({x, y, z, metricClosureRepresentative (fA k) x} :
       Set A) ⊆ C ∧
    (∀ t : ℝ, ∀ c : C,
      Option.map Subtype.val (fC t c) = fA t c.val) ∧
    MetricOn S dV ∧
    (∀ t : ℝ, Jump S t →
      @MetricJumpClosureLaw V o dV (fV t) t) ∧
    Function.Injective e ∧
    (∀ t : ℝ, ∀ c : C,
      fV t (e c) = Option.map e (fC t c))

/-- Exact function-closed subset completion gives the full local
four-point composition test, with no globally injective map on A. -/
theorem metricFourPointCompositionLocalTest_of_closedSubset
    {S : Set ℝ} {A : Type u}
    (fA : ℝ → A → Option A)
    (j k : ℝ) (x y z : A)
    (hCompletion :
      MetricFourPointCompositionClosedSubsetCompletion S
        fA j k x y z) :
    MetricFourPointCompositionLocalTest S fA j k x y z := by
  classical
  obtain ⟨C, fC, V, o, dV, fV, e,
    hSupport, hRestrict, hdV, hLaw, hInj, hFunctions⟩ :=
    hCompletion
  have hx : x ∈ C := hSupport (by simp)
  have hy : y ∈ C := hSupport (by simp)
  let i : A → V :=
    fun a => if ha : a ∈ C then e ⟨a, ha⟩ else e ⟨x, hx⟩
  have hi (c : C) : i c.val = e c := by
    dsimp [i]
    simp only [dif_pos c.property]
  have hOption (t : ℝ) (c : C) :
      fV t (i c.val) = Option.map i (fA t c.val) := by
    calc
      fV t (i c.val) = fV t (e c) := by rw [hi c]
      _ = Option.map e (fC t c) := hFunctions t c
      _ = Option.map i (fA t c.val) := by
        rw [← hRestrict t c]
        cases h : fC t c with
        | none => simp [h]
        | some z => simp [h, hi z]
  refine ⟨V, o, dV, fV, i, hdV, hLaw, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have haC : a ∈ C := hSupport ha
    have hbC : b ∈ C := hSupport hb
    have hE : e ⟨a, haC⟩ = e ⟨b, hbC⟩ := by
      calc
        e ⟨a, haC⟩ = i a := (hi ⟨a, haC⟩).symm
        _ = i b := hab
        _ = e ⟨b, hbC⟩ := hi ⟨b, hbC⟩
    exact congrArg Subtype.val (hInj hE)
  · exact hOption j ⟨x, hx⟩
  · exact hOption k ⟨y, hy⟩
  · exact hOption k ⟨x, hx⟩

/-- One exact function-closed local completion forces the
normal form in the original WEAK candidate, despite the
candidate not having any metric of its own. -/
theorem metricCandidateComposition_normalform_of_closedSubset
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (j k : ℝ) (hj : Jump S j) (hk : Jump S k)
    (x y z : A)
    (hxy : fA j x = some y) (hyz : fA k y = some z)
    (hCompletion :
      MetricFourPointCompositionClosedSubsetCompletion S
        fA j k x y z) :
    j < k ∧ fA k x = some z := by
  apply metricJumpComposition_normalform_of_localTest
    hpos fA j k hj hk x y z hxy hyz
  exact metricFourPointCompositionLocalTest_of_closedSubset
    fA j k x y z hCompletion

/-- If every defined two-step composition in the candidate
has its own (possibly differently targeted) function-closed
local completion, the candidate satisfies the strict-height
normal form globally on the specified jump levels. -/
theorem metricCandidateComposition_normalform_of_closedSubsetTests
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u} (fA : ℝ → A → Option A)
    (J : Set ℝ)
    (hJ : ∀ j ∈ J, Jump S j)
    (hLocal : ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
      fA j x = some y → fA k y = some z →
        MetricFourPointCompositionClosedSubsetCompletion S
          fA j k x y z) :
    ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : A,
      fA j x = some y → fA k y = some z →
        j < k ∧ fA k x = some z := by
  intro j hj k hk x y z hxy hyz
  exact metricCandidateComposition_normalform_of_closedSubset
    hpos fA j k (hJ j hj) (hJ k hk)
    x y z hxy hyz (hLocal j hj k hk x y z hxy hyz)

end AllThoseRamseyClasses.Applications.MetricSaturation
