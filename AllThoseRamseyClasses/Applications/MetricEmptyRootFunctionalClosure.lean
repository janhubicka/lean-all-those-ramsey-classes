import AllThoseRamseyClasses.Applications.MetricEmptyBaseOrderedAmalgamation
import AllThoseRamseyClasses.Applications.MetricFunctionalJumpClosureLaw

/-!
# Exact partial F_j closure laws in empty-root S-metric amalgamation

When the common root is empty, the correct strong metric amalgam
uses the disjoint union U ⊕ V and assigns every cross-side pair
the maximal allowed distance m. A proper jump j is strictly below m,
so no j-class can meet both sides.

Gluing a partial Option-valued F_j on each side as the disjoint
sum of its original partial functions therefore preserves the
EXACT source class law: each class has its same undefined last
closure point, every other member maps to it, and its distance
to the closure is exactly j. Definedness and undefinedness on
both old sides are unchanged.

This closes the functional F_j CLASS-LAW COMPONENT over the
empty root, separately from the finite nonempty-root proof.
It does not yet establish the full metric Ramsey theorem or the
printed local weak-candidate completion cutoff.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Exact disjoint sum of Option-valued partial unary functions,
with no new function value or identification between the parts. -/
def separatedSumPartialFunction
    {U : Type u} {V : Type v}
    (fU : U → Option U) (fV : V → Option V) :
    (U ⊕ V) → Option (U ⊕ V)
  | .inl x => Option.map Sum.inl (fU x)
  | .inr z => Option.map Sum.inr (fV z)

@[simp] theorem separatedSumPartialFunction_left
    {U : Type u} {V : Type v}
    (fU : U → Option U) (fV : V → Option V)
    (x : U) :
    separatedSumPartialFunction fU fV (.inl x) =
      Option.map Sum.inl (fU x) := rfl

@[simp] theorem separatedSumPartialFunction_right
    {U : Type u} {V : Type v}
    (fU : U → Option U) (fV : V → Option V)
    (z : V) :
    separatedSumPartialFunction fU fV (.inr z) =
      Option.map Sum.inr (fV z) := rfl

/-- The printed per-jump F_j law is preserved without additions
when the two metrics are glued over the EMPTY base at their
common maximum allowed S-distance. Neither summand is assumed
nonempty and no cross-part proper-jump class is possible. -/
theorem separatedSumPartialFunction_jumpClosureLaw
    {S : Set ℝ}
    {U : Type u} {V : Type v}
    [LinearOrder U] [LinearOrder V]
    (m : ℝ) (hmax : ∀ s ∈ S, s ≤ m)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (j : ℝ) (hj : Jump S j)
    (fU : U → Option U) (fV : V → Option V)
    (hLawU : MetricJumpClosureLaw dU fU j)
    (hLawV : MetricJumpClosureLaw dV fV j) :
    (letI := separatedSumLinearOrder (U := U) (V := V);
      MetricJumpClosureLaw
        (separatedSumDistance m dU dV)
        (separatedSumPartialFunction fU fV) j) := by
  letI : LinearOrder (U ⊕ V) := separatedSumLinearOrder
  intro x
  cases x with
  | inl x =>
      obtain ⟨c, hxc, hcNone, hClass⟩ := hLawU x
      refine ⟨.inl c, hxc, ?_, ?_⟩
      · simp [separatedSumPartialFunction, hcNone]
      · intro y hy
        cases y with
        | inl y =>
            change dU y x ≤ j at hy
            rcases hClass y hy with hEq | ⟨hBefore, hDist, hVal⟩
            · exact Or.inl (congrArg Sum.inl hEq)
            · refine Or.inr ⟨?_, hDist, ?_⟩
              · change
                  @LT.lt (Lex (U ⊕ V))
                    (separatedSumLexOrder (U := U) (V := V)).toLT
                    (toLex (Sum.inl y : U ⊕ V))
                    (toLex (Sum.inl c : U ⊕ V))
                exact Sum.Lex.inl_lt_inl_iff.mpr hBefore
              · simp [separatedSumPartialFunction, hVal]
        | inr y =>
            change m ≤ j at hy
            exact False.elim ((not_le.mpr (jump_lt_max hmax hj)) hy)
  | inr z =>
      obtain ⟨c, hzc, hcNone, hClass⟩ := hLawV z
      refine ⟨.inr c, hzc, ?_, ?_⟩
      · simp [separatedSumPartialFunction, hcNone]
      · intro y hy
        cases y with
        | inl x =>
            change m ≤ j at hy
            exact False.elim ((not_le.mpr (jump_lt_max hmax hj)) hy)
        | inr y =>
            change dV y z ≤ j at hy
            rcases hClass y hy with hEq | ⟨hBefore, hDist, hVal⟩
            · exact Or.inl (congrArg Sum.inr hEq)
            · refine Or.inr ⟨?_, hDist, ?_⟩
              · change
                  @LT.lt (Lex (U ⊕ V))
                    (separatedSumLexOrder (U := U) (V := V)).toLT
                    (toLex (Sum.inr y : U ⊕ V))
                    (toLex (Sum.inr c : U ⊕ V))
                exact Sum.Lex.inr_lt_inr_iff.mpr hBefore
              · simp [separatedSumPartialFunction, hVal]

end AllThoseRamseyClasses.Applications.MetricSaturation
