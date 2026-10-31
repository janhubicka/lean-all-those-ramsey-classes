import AllThoseRamseyClasses.Lifts.GlobalFlipLocalRightSupport

/-!
# Section 3 Claim 2: finite contextual B-support descent

A successful actual inner B-to-A flip has already been shown to
strictly decrease the number of B-only SOURCE vertices *inside*
the transported outer context, provided the same old/new target
maps agree on the unchanged complement:
`geometricInnerSubpiece_strict_localRightSupport_of_global`.

This file isolates the **iteration** of such a descent. The state
must include an actual forbidden source, its EHN map, a genuine
geometric outer piece, the original ordered root coordinates and
its complete rooted forbidden-diagram incompatibility profile.
The latter two cannot be replaced by a mere closed vertex set or
a single forbidden-family membership test.

Theorems below are logically unconditional FINITE-DESCENT
principles, but their application to the printed Claim 2 is
conditional on a certified contextual successor relation:
* its next state is again a genuine geometric outer piece;
* its original outer root coordinates are fixed;
* its FULL all-test incompatibility profile is fixed;
* its original exterior is unchanged;
* its local B-only SOURCE count strictly drops.

The current source library proves several parts of one actual
replacement separately. It does NOT yet construct successors
satisfying all these requirements, or prove the final A-to-B
contradiction at a terminal state. In particular, NO "another
flippable subpiece exists" premise is hidden in these statements.
-/

namespace AllThoseRamseyClasses.Lifts

/-- Every sequence of admissible contextual moves with a strictly
decreasing natural-number rank reaches a terminal state.

The terminal conclusion is genuine: it has NO successor under
`Step`, rather than presupposing a next successful flip. The
reflexive-transitive closure records an actual finite sequence
from the original state; no finiteness of the space of states
or fixed source-carrier type is needed. -/
theorem claim2_exists_terminal_of_strict_localB_descent
    {State : Type*}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount : State → ℕ)
    (hStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s)
    {initial : State} (hInitial : Valid initial) :
    ∃ terminal : State,
      Valid terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      ¬ ∃ next : State, Step terminal next := by
  classical
  have descend :
      ∀ n : ℕ, ∀ s : State,
        Valid s → localBCount s = n →
        ∃ t : State, Valid t ∧
          Relation.ReflTransGen Step s t ∧
          ¬ ∃ next : State, Step t next := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hCount
      by_cases hNext : ∃ t : State, Step s t
      · obtain ⟨t, hst⟩ := hNext
        obtain ⟨ht, hStrict⟩ := hStep hs hst
        have htLower : localBCount t < n := by
          rw [← hCount]
          exact hStrict
        obtain ⟨u, hu, hReach, hTerminal⟩ :=
          ih (localBCount t) htLower t ht rfl
        have hOne : Relation.ReflTransGen Step s t :=
          Relation.ReflTransGen.single hst
        exact ⟨u, hu, hOne.trans hReach, hTerminal⟩
      · exact ⟨s, hs, Relation.ReflTransGen.refl, hNext⟩
  exact descend (localBCount initial) initial hInitial rfl

/-- The explicit four-obligation interface for the printed Claim 2.

In any concrete application `Geometric` must assert a GENUINE
geometric minimal-separator piece, `RootFixed` the original
root and target coordinates, `ProfileFixed` the complete
all-test incompatibility profile, and `ExteriorFixed` the
unchanged full native functional exterior.

The step hypothesis is NOT proved by this theorem. In
particular the one-step closed-context and support lemmas do
not yet establish `Geometric` or `ProfileFixed` after a flip.
These predicates are separate specifically so an erroneous
conflation of the four claims is visible in the statement. -/
theorem claim2_exists_terminal_preserving_outer_invariants
    {State : Type*}
    (Geometric RootFixed ProfileFixed ExteriorFixed : State → Prop)
    (Step : State → State → Prop)
    (localBCount : State → ℕ)
    (hStep : ∀ s t : State,
      Geometric s → RootFixed s → ProfileFixed s →
      ExteriorFixed s → Step s t →
        Geometric t ∧ RootFixed t ∧ ProfileFixed t ∧
        ExteriorFixed t ∧ localBCount t < localBCount s)
    {initial : State}
    (hGeometric : Geometric initial)
    (hRoot : RootFixed initial)
    (hProfile : ProfileFixed initial)
    (hExterior : ExteriorFixed initial) :
    ∃ terminal : State,
      Geometric terminal ∧ RootFixed terminal ∧
      ProfileFixed terminal ∧ ExteriorFixed terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      ¬ ∃ next : State, Step terminal next := by
  let Valid : State → Prop := fun s =>
    Geometric s ∧ RootFixed s ∧ ProfileFixed s ∧ ExteriorFixed s
  have hValidStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s := by
    intro s t hs hst
    rcases hs with ⟨hsG, hsR, hsP, hsE⟩
    obtain ⟨htG, htR, htP, htE, htCount⟩ :=
      hStep s t hsG hsR hsP hsE hst
    exact ⟨⟨htG, htR, htP, htE⟩, htCount⟩
  obtain ⟨terminal, hValid, hPath, hNoStep⟩ :=
    claim2_exists_terminal_of_strict_localB_descent
      Valid Step localBCount hValidStep
      ⟨hGeometric, hRoot, hProfile, hExterior⟩
  exact ⟨terminal, hValid.1, hValid.2.1,
    hValid.2.2.1, hValid.2.2.2, hPath, hNoStep⟩

/-- The final contradiction uses a SEPARATE exit lemma. To apply
this to Claim 2 one must prove that every terminal context with
all four invariants contradicts the original left-support
minimality (typically via a final A-to-B flip). Merely proving
strict local B-descent does not supply that exit lemma. -/
theorem claim2_no_valid_initial_of_terminal_exit
    {State : Type*}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount : State → ℕ)
    (hStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s)
    (hExit : ∀ s : State,
      Valid s → (¬ ∃ t : State, Step s t) → False) :
    ¬ ∃ initial : State, Valid initial := by
  rintro ⟨initial, hInitial⟩
  obtain ⟨terminal, hValid, _hPath, hNoStep⟩ :=
    claim2_exists_terminal_of_strict_localB_descent
      Valid Step localBCount hStep hInitial
  exact hExit terminal hValid hNoStep

end AllThoseRamseyClasses.Lifts
