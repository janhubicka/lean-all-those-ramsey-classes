import AllThoseRamseyClasses.Applications.MetricJumpClosureComposition
import Mathlib.Tactic

/-!
# Finite normal-form hull of prescribed metric closure functions

For any finite set J of genuine proper jump levels, a valid metric
functional structure has a bounded closure orbit of EACH seed x.
Put

  orbit_J(x) = {x} ∪ { F_j(x) : j∈J, F_j(x) is defined }.

This finite set is closed under every F_i with i∈J, because the
validated two-step composition normal form says each defined
F_i(F_j(x)) is already the direct value F_i(x). Moreover

  |orbit_J(x)| ≤ |J| + 1,

and the union of two such orbits has size ≤ 2(|J|+1).

These are exact finite closure estimates for VALID structures
satisfying all printed F_j closure laws. They do not establish
that an arbitrary weak candidate satisfies the same identities,
nor that every U-closed induced test contains this orbit.
Transferring the normal form through local weak completions
without exceeding the printed cutoff is separate work.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- At most one direct F_j representative per jump level,
with undefined values harmlessly mapped back to the seed. -/
noncomputable def metricOneStepJumpOrbit
    {V : Type u}
    (J : Finset ℝ)
    (f : ℝ → V → Option V)
    (x : V) : Finset V := by
  classical
  exact insert x (J.image (fun j => (f j x).getD x))

/-- Every defined direct F_j value appears in the finite orbit. -/
theorem metricOneStepJumpOrbit_mem_of_some
    {V : Type u}
    (J : Finset ℝ)
    (f : ℝ → V → Option V)
    (x : V)
    (j : ℝ) (hj : j ∈ J)
    (y : V) (hjy : f j x = some y) :
    y ∈ metricOneStepJumpOrbit J f x := by
  classical
  unfold metricOneStepJumpOrbit
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨j, hj, by simp [hjy]⟩

/-- The orbit of one seed contains at most one vertex
per jump level, plus the seed. No metric law is
needed for this raw counting estimate. -/
theorem metricOneStepJumpOrbit_card_le
    {V : Type u}
    (J : Finset ℝ)
    (f : ℝ → V → Option V)
    (x : V) :
    (metricOneStepJumpOrbit J f x).card ≤ J.card + 1 := by
  classical
  unfold metricOneStepJumpOrbit
  calc
    (insert x (J.image (fun j => (f j x).getD x))).card ≤
        (J.image (fun j => (f j x).getD x)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ J.card + 1 := Nat.add_le_add_right Finset.card_image_le _

/-- In a VALID metric expansion the finite one-step orbit is
already closed under all the F_i for i∈J. In particular
repeated defined function compositions cannot create
any new vertex beyond the direct representatives. -/
theorem metricOneStepJumpOrbit_closed
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (f : ℝ → V → Option V)
    (hLaw : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw d (f j) j)
    (J : Finset ℝ)
    (hJump : ∀ j ∈ J, Jump S j)
    (x y z : V)
    (hy : y ∈ metricOneStepJumpOrbit J f x)
    (i : ℝ) (hi : i ∈ J)
    (hiz : f i y = some z) :
    z ∈ metricOneStepJumpOrbit J f x := by
  classical
  unfold metricOneStepJumpOrbit at hy
  rcases Finset.mem_insert.mp hy with hRoot | hOther
  · subst y
    exact metricOneStepJumpOrbit_mem_of_some J f x i hi z hiz
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hOther
    cases hfj : f j x with
    | none =>
        have hDirect : f i x = some z := by
          simpa [hfj] using hiz
        exact metricOneStepJumpOrbit_mem_of_some J f x i hi z hDirect
    | some v =>
        have hSecond : f i v = some z := by
          simpa [hfj] using hiz
        have hNormal : f i x = some z :=
          (metricJumpClosureLaw_defined_composition_normalform
            hpos hd f hLaw j i (hJump j hj) (hJump i hi)
            x v z hfj hSecond).2
        exact metricOneStepJumpOrbit_mem_of_some J f x i hi z hNormal

/-- The union of two function-closed seed orbits has at most
2(|J|+1) vertices, before any additional path/cycle vertices.
This is the numerical functional-closure factor in the
candidate bound of the printed metric application. -/
theorem metricTwoOneStepJumpOrbits_card_le
    {V : Type u} [DecidableEq V]
    (J : Finset ℝ)
    (f : ℝ → V → Option V)
    (x y : V) :
    ((metricOneStepJumpOrbit J f x) ∪
      (metricOneStepJumpOrbit J f y)).card ≤
        2 * (J.card + 1) := by
  have hu := Finset.card_union_le
    (metricOneStepJumpOrbit J f x)
    (metricOneStepJumpOrbit J f y)
  have hx := metricOneStepJumpOrbit_card_le J f x
  have hy := metricOneStepJumpOrbit_card_le J f y
  omega

/-- Union of the two orbits stays function-closed under the
valid metric F_j laws. The two seeds need not be close or
in the same proper-jump equivalence class. -/
theorem metricTwoOneStepJumpOrbits_closed
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (f : ℝ → V → Option V)
    (hLaw : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw d (f j) j)
    (J : Finset ℝ)
    (hJump : ∀ j ∈ J, Jump S j)
    (x y z w : V)
    (hz : z ∈ (metricOneStepJumpOrbit J f x) ∪
        (metricOneStepJumpOrbit J f y))
    (j : ℝ) (hj : j ∈ J)
    (hw : f j z = some w) :
    w ∈ (metricOneStepJumpOrbit J f x) ∪
        (metricOneStepJumpOrbit J f y) := by
  rcases Finset.mem_union.mp hz with hLeft | hRight
  · exact Finset.mem_union.mpr (Or.inl
      (metricOneStepJumpOrbit_closed hpos hd f hLaw J hJump
        x z w hLeft j hj hw))
  · exact Finset.mem_union.mpr (Or.inr
      (metricOneStepJumpOrbit_closed hpos hd f hLaw J hJump
        y z w hRight j hj hw))

end AllThoseRamseyClasses.Applications.MetricSaturation
