import AllThoseRamseyClasses.Applications.MetricFiniteBaseCrossSymmetry
import AllThoseRamseyClasses.Applications.MetricJumpSamedist

/-!
# Rooted S-metric interpretation of the attained finite-base crossing

The shortest rounded path `min_{a∈A} (dU(x,iU(a)) ⊕ dV(iV(a),y))`
is an ACTUAL cross-distance candidate between two endpoints outside
the identified base. Its legs are in S because each endpoint is
distinct from every base vertex on its own side.

The generic finite-minimum lemmas now apply without independently
assuming that either leg is S-valued. They give:

* the positive S-valuedness of the proposed cross distance;
* its exact j-threshold criterion for every proper jump j;
* the same result for arbitrary finite nonempty roots, including
  nonsurjective base embeddings and arbitrary metric vertex carriers.

No assumption is made here that the two side metrics agree on the
base, because only the **two-edge candidate set** is studied.
The actual pushout metric and full strong-amalgamation/ordering
lemmas still require that compatibility hypothesis separately.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Actual rounded shortest cross distance from x on the first
metric side to y on the second side, indexed by a finite nonempty
common root A (whose embeddings need not be surjective). -/
noncomputable def finiteMetricBaseCrossDistance
    (S : Set ℝ) {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    (dU : U → U → ℝ) (dV : V → V → ℝ)
    (iU : A → U) (iV : A → V)
    (x : U) (y : V) : ℝ :=
  finiteBaseShortestDistance S
    (fun a => dU x (iU a)) (fun a => dV (iV a) y)

/-- The proposed cross-side length is a genuinely positive allowed
distance whenever both endpoints lie outside the image of the common
root. This discharges all positivity/S-membership premises from
the actual metric laws of the original sides. -/
theorem finiteMetricBaseCrossDistance_pos_mem
    {S : Set ℝ} (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (x : U) (y : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hy : ∀ a : A, iV a ≠ y) :
    finiteMetricBaseCrossDistance S dU dV iU iV x y ∈ S ∧
      0 < finiteMetricBaseCrossDistance S dU dV iU iV x y := by
  have hp : ∀ a : A, dU x (iU a) ∈ S :=
    fun a => hdU.values x (iU a) (hx a)
  have hq : ∀ a : A, dV (iV a) y ∈ S :=
    fun a => hdV.values (iV a) y (hy a)
  have hMem : finiteMetricBaseCrossDistance S dU dV iU iV x y ∈ S :=
    finiteBaseShortestDistance_mem hS
      (fun a => dU x (iU a)) (fun a => dV (iV a) y) hp hq
  exact ⟨hMem, hpos _ hMem⟩

/-- A proper jump j connects the two off-base endpoints through
the finite rounded shortest-path metric exactly when there is one
common root vertex whose images are j-close to both endpoints.
This statement is the geometric form required when tracking
j-equivalence classes across a nonempty metric amalgamation base. -/
theorem finiteMetricBaseCrossDistance_le_jump_iff
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (iU : A → U) (iV : A → V)
    (x : U) (y : V)
    (hx : ∀ a : A, x ≠ iU a)
    (hy : ∀ a : A, iV a ≠ y)
    (j : ℝ) (hj : Jump S j) :
    finiteMetricBaseCrossDistance S dU dV iU iV x y ≤ j ↔
      ∃ a : A, dU x (iU a) ≤ j ∧ dV (iV a) y ≤ j := by
  have hp : ∀ a : A, dU x (iU a) ∈ S :=
    fun a => hdU.values x (iU a) (hx a)
  have hq : ∀ a : A, dV (iV a) y ∈ S :=
    fun a => hdV.values (iV a) y (hy a)
  exact finiteBaseShortestDistance_le_jump_iff_witness
    hpos (fun a => dU x (iU a)) (fun a => dV (iV a) y)
    hp hq j hj

end AllThoseRamseyClasses.Applications.MetricSaturation
