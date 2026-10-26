import AllThoseRamseyClasses.Applications.MetricEmptyRootFunctionalClosure
import AllThoseRamseyClasses.Applications.MetricEmptyBaseOrderedAmalgamation

/-!
# Full finite S-metric functional strong amalgam over an EMPTY root

This assembles the previously separately certified empty-root
components into one exact, reusable exported theorem.
For finite positive four-values S with a chosen largest
allowed distance m, and two finite source structures
satisfying the paper's literal ordered metric and F_j
class laws, their disjoint union has:
* a genuine S-metric preserving both sides;
* one linear order preserving BOTH old complete orders;
* literal convexity for the paper's block equivalences;
* every original F_j value and undefined value unchanged;
* the FULL designated-last closure law for EVERY proper jump;
* exact strong disjointness of the original summands.

No nonempty base or shortest-path minimum over an empty family
is invented. The case S=empty cannot satisfy strong
amalgamation over the empty root for two singletons.

This theorem covers only the EMPTY root. The corresponding
nonempty-root functional strong amalgam is
metricRooted_finiteS_functionalStrongAmalgam_exists.
Neither theorem verifies the printed bounded-cycle argument
or exact weak-candidate local-completion cutoff.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Complete strong amalgamation in the printed finite ordered
S-metric partial-function language, over the EMPTY root.
The exact induced option-function restrictions are recorded on
both sides, not inferred from preservation of defined values. -/
theorem separatedSum_finiteS_functionalStrongAmalgam_exists
    {S : Set ℝ}
    (hfinite : S.Finite) (hpos : Positive S)
    (h4 : FourValues S)
    (m : ℝ) (hm : m ∈ S)
    (hmax : ∀ s ∈ S, s ≤ m)
    {U : Type u} {V : Type v}
    [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hconvU : PaperBlockConvex S dU)
    (hconvV : PaperBlockConvex S dV)
    (fU : ℝ → U → Option U)
    (fV : ℝ → V → Option V)
    (hLawU : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw dU (fU j) j)
    (hLawV : ∀ j : ℝ, Jump S j →
      MetricJumpClosureLaw dV (fV j) j) :
    ∃ (o : LinearOrder (U ⊕ V))
      (fW : ℝ → (U ⊕ V) → Option (U ⊕ V)),
      (∀ x y : U,
        @LE.le (U ⊕ V) o.toLE (.inl x) (.inl y) ↔ x ≤ y) ∧
      (∀ z t : V,
        @LE.le (U ⊕ V) o.toLE (.inr z) (.inr t) ↔ z ≤ t) ∧
      (@PaperBlockConvex (U ⊕ V) o S
        (separatedSumDistance m dU dV)) ∧
      MetricOn S (separatedSumDistance m dU dV) ∧
      (∀ j : ℝ, Jump S j →
        @MetricJumpClosureLaw (U ⊕ V) o
          (separatedSumDistance m dU dV) (fW j) j) ∧
      (∀ j : ℝ, Jump S j → ∀ x : U,
        fW j (.inl x) = Option.map Sum.inl (fU j x)) ∧
      (∀ j : ℝ, Jump S j → ∀ z : V,
        fW j (.inr z) = Option.map Sum.inr (fV j z)) ∧
      (∀ x : U, ∀ z : V,
        (Sum.inl x : U ⊕ V) ≠ .inr z) ∧
      (∀ x y : U,
        separatedSumDistance m dU dV (.inl x) (.inl y) = dU x y) ∧
      (∀ z t : V,
        separatedSumDistance m dU dV (.inr z) (.inr t) = dV z t) := by
  classical
  let o : LinearOrder (U ⊕ V) := separatedSumLinearOrder
  let fW : ℝ → (U ⊕ V) → Option (U ⊕ V) :=
    fun j => separatedSumPartialFunction (fU j) (fV j)
  have hMetric : MetricOn S (separatedSumDistance m dU dV) :=
    separatedSumDistance_metric hpos m hm hmax hdU hdV
  have hBlock : @PaperBlockConvex (U ⊕ V) o S
      (separatedSumDistance m dU dV) :=
    separatedSumDistance_paperBlockConvex
      hfinite hpos h4 m hm hmax hdU hdV hconvU hconvV
  refine ⟨o, fW, ?_, ?_, hBlock, hMetric, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact separatedSumLinearOrder_inl_le_inl_iff x y
  · intro z t
    exact separatedSumLinearOrder_inr_le_inr_iff z t
  · intro j hj
    exact separatedSumPartialFunction_jumpClosureLaw
      m hmax j hj (fU j) (fV j) (hLawU j hj) (hLawV j hj)
  · intro j hj x
    rfl
  · intro j hj z
    rfl
  · intro x z h
    cases h
  · intro x y
    rfl
  · intro z t
    rfl

end AllThoseRamseyClasses.Applications.MetricSaturation
