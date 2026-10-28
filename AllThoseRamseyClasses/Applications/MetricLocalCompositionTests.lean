import AllThoseRamseyClasses.Applications.MetricJumpClosureComposition
import AllThoseRamseyClasses.Applications.MetricLocalClosureCoherence

/-!
# Transfer the F_j composition normal form through local four-point tests

The normal-form law F_k(F_j(x))=F_k(x) for a defined two-step
composition was proved for VALID metric-functional targets.

A weak candidate need not itself be a valid metric. Nevertheless,
a LOCAL completion of only the relevant Option-function data
can force the SAME composition law in the original source.

Suppose the source prescribes F_j(x)=y and F_k(y)=z.
One may complete a test on the four original vertices

    {x, y, z, rep_k(x)}

to a valid target, preserving the three actual function values
F_j(x), F_k(y), F_k(x), including undefinedness of the last.
Injectivity of the local map is needed ONLY on those four points.

The target normal form forces j<k and F_k(x)=z back in the
source. The metric target, order and local map may be different
for every such pair. No global candidate embedding is needed.

**Source-proof boundary:** The manuscript's weak U-closed
local-completion axiom must still be shown to supply these
particular tests with controlled function-closed supports
of the allowed cardinality. We do not assume that conclusion.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- A local completion into any valid S-metric functional
target transfers a two-step F_j composition equation back to
the original weak candidate, with injectivity required only
on the four named old vertices.

No metric property of the source is assumed or proved. -/
theorem metricJumpComposition_normalform_of_fourPointCompletion
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u} {V : Type v} [LinearOrder V]
    (fA : ℝ → A → Option A)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    (fV : ℝ → V → Option V)
    (hLawV : ∀ t : ℝ, Jump S t →
      MetricJumpClosureLaw dV (fV t) t)
    (i : A → V)
    (j k : ℝ) (hj : Jump S j) (hk : Jump S k)
    (x y z : A)
    (hSourceJ : fA j x = some y)
    (hSourceK : fA k y = some z)
    (hInj : Set.InjOn i
      ({x, y, z, metricClosureRepresentative (fA k) x} : Set A))
    (hExactJ : fV j (i x) = Option.map i (fA j x))
    (hExactKY : fV k (i y) = Option.map i (fA k y))
    (hExactKX : fV k (i x) = Option.map i (fA k x)) :
    j < k ∧ fA k x = some z := by
  have hTargetJ : fV j (i x) = some (i y) := by
    simpa [hSourceJ] using hExactJ
  have hTargetK : fV k (i y) = some (i z) := by
    simpa [hSourceK] using hExactKY
  obtain ⟨hjk, hTargetDirect⟩ :=
    metricJumpClosureLaw_defined_composition_normalform
      hpos hdV fV hLawV j k hj hk
      (i x) (i y) (i z) hTargetJ hTargetK
  have hCandidate : Option.map i (fA k x) = some (i z) :=
    hExactKX.symm.trans hTargetDirect
  cases hSourceDirect : fA k x with
  | none =>
      simp [hSourceDirect] at hCandidate
  | some w =>
      have hiw : i w = i z :=
        Option.some.inj (by simpa [hSourceDirect] using hCandidate)
      have hw : w ∈
          ({x, y, z, metricClosureRepresentative (fA k) x} :
            Set A) := by
        simp [metricClosureRepresentative, hSourceDirect]
      have hz :
          z ∈ ({x, y, z, metricClosureRepresentative (fA k) x} :
            Set A) := by simp
      have hwz : w = z := hInj hw hz hiw
      subst w
      exact ⟨hjk, hSourceDirect⟩

/-- Each F_j composition test may use an independent ordered
target S-metric, a different total map on the candidate,
and local injectivity only on the explicit four-point support. -/
def MetricFourPointCompositionLocalTest
    (S : Set ℝ)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (j k : ℝ) (x y z : A) : Prop :=
  ∃ (V : Type u) (o : LinearOrder V)
    (dV : V → V → ℝ) (fV : ℝ → V → Option V)
    (i : A → V),
    MetricOn S dV ∧
    (∀ t : ℝ, Jump S t →
      @MetricJumpClosureLaw V o dV (fV t) t) ∧
    Set.InjOn i
      ({x, y, z, metricClosureRepresentative (fA k) x} : Set A) ∧
    fV j (i x) = Option.map i (fA j x) ∧
    fV k (i y) = Option.map i (fA k y) ∧
    fV k (i x) = Option.map i (fA k x)

/-- A varying-target four-point composition test forces
strictly increasing jump levels and the SAME higher-level
direct F_k-value in the original weak source. -/
theorem metricJumpComposition_normalform_of_localTest
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u}
    (fA : ℝ → A → Option A)
    (j k : ℝ) (hj : Jump S j) (hk : Jump S k)
    (x y z : A)
    (hjx : fA j x = some y)
    (hky : fA k y = some z)
    (hLocal :
      MetricFourPointCompositionLocalTest S fA j k x y z) :
    j < k ∧ fA k x = some z := by
  obtain ⟨V, o, dV, fV, i, hdV, hLaw,
    hInj, hJ, hKY, hKX⟩ := hLocal
  letI : LinearOrder V := o
  exact metricJumpComposition_normalform_of_fourPointCompletion
    hpos fA hdV fV hLaw i j k hj hk x y z
    hjx hky hInj hJ hKY hKX

end AllThoseRamseyClasses.Applications.MetricSaturation
