import AllThoseRamseyClasses.Applications.MetricFunctionalJumpClosureLaw

/-!
# Functional closure targets of proper metric jump classes

The 2019 auxiliary metric lift prescribes a partial unary operation
F_j on every proper jump class. Its defined values must point at
the unique last member of the class, at exact distance j, where
the operation becomes undefined.

This file derives that exact consequence from the source's
already formalized closure law. It also shows that a closed root
cannot send a root vertex to a closure point outside the root:
when the source F_j value is defined, its target lies in the
common root and is itself an undefined closure point.

These lemmas do not construct an amalgam or verify the source
local-completion cutoff. They isolate source-function facts
needed to verify the glued operations without unmentioned
closure assumptions.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Every defined F_j(x)=c points to the actual class-last
vertex c; that target is undefined and the edge has exactly
length j. The point x itself is strictly before c. -/
theorem metricJumpClosureLaw_some_is_target
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ}
    (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (x c : V) (hSome : f x = some c) :
    f c = none ∧ x < c ∧ d x c = j := by
  obtain ⟨m, _, hNone, hClass⟩ := hLaw x
  have hxx : d x x ≤ j := by
    rw [hd.diag x]
    exact (hpos j hj.1).le
  rcases hClass x hxx with heq | ⟨hBefore, hDistance, hTarget⟩
  · subst x
    rw [hNone] at hSome
    cases hSome
  · have hmc : m = c :=
      Option.some.inj (hTarget.symm.trans hSome)
    subst c
    exact ⟨hNone, hBefore, hDistance⟩

/-- At a vertex with undefined F_j, every other point in
the class maps to that vertex, as well as lying strictly
before it at exact distance j. -/
theorem metricJumpClosureLaw_none_is_exact_target
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ}
    (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (c : V) (hNone : f c = none)
    (x : V) (hDifferent : x ≠ c)
    (hClose : d x c ≤ j) :
    x < c ∧ d x c = j ∧ f x = some c := by
  obtain ⟨m, _, _hmNone, hClass⟩ := hLaw c
  have hcc : d c c ≤ j := by
    rw [hd.diag c]
    exact (hpos j hj.1).le
  have hcm : c = m := by
    rcases hClass c hcc with heq | ⟨_, _, hSome⟩
    · exact heq
    · rw [hNone] at hSome
      cases hSome
  rcases hClass x hClose with heq | ⟨hBefore, hDistance, hSome⟩
  · exact False.elim (hDifferent (heq.trans hcm.symm))
  · rw [← hcm] at hBefore hDistance hSome
    exact ⟨hBefore, hDistance, hSome⟩

/-- A partial-function embedding of a closed root forces the
closure of each original root point to remain in that root.
The returned root closure is an undefined F_j point whose
distance from the original point is at most j. -/
theorem metricRootClosure_target_inside_closed_root
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u} {U : Type v}
    [LinearOrder U]
    {dU : U → U → ℝ}
    (hdU : MetricOn S dU)
    (j : ℝ) (hj : Jump S j)
    (i : A → U)
    (fA : A → Option A)
    (fU : U → Option U)
    (hExt : ∀ a : A,
      fU (i a) = Option.map i (fA a))
    (hLawU : MetricJumpClosureLaw dU fU j)
    (a : A) :
    ∃ c : A,
      fA c = none ∧ dU (i a) (i c) ≤ j ∧
      (a = c ∨ fA a = some c) := by
  cases h : fA a with
  | none =>
      refine ⟨a, h, ?_, Or.inl rfl⟩
      rw [hdU.diag (i a)]
      exact (hpos j hj.1).le
  | some c =>
      have hSome : fU (i a) = some (i c) := by
        rw [hExt a, h]
        rfl
      obtain ⟨hNone, _, hDistance⟩ :=
        metricJumpClosureLaw_some_is_target
          hpos hdU j hj fU hLawU (i a) (i c) hSome
      have hRootNone : fA c = none := by
        rw [hExt c] at hNone
        cases hc : fA c with
        | none => exact hc
        | some x =>
            simp [hc] at hNone
      exact ⟨c, hRootNone, le_of_eq hDistance, Or.inr h⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
