import AllThoseRamseyClasses.Lifts.Claim2TerminalLeftSupportAccounting

/-!
# Track C: a finite descent must reach an explicit obstruction or zero exit

The verified Claim 2 terminal theorem reaches rank zero IF all
positive-rank valid states admit a successor. A more diagnostic
alternative uses a *verified local trichotomy*: every positive-rank
valid state either has an actual strict source step or exhibits
a separate obstruction (for instance a smaller mixed root or a
weak target-map seam collision).

Define the restricted step relation to permit movement only
FROM a non-obstructed state. The already checked well-founded
rank descent reaches a terminal state in this restricted relation,
with exactly unchanged exterior A-exclusive SOURCE count.
If that state has rank zero, an independently established genuine
zero-exit contradicts the ORIGINAL minimizer; if it has positive
rank, the local alternative forces an obstruction, since
a successor would contradict terminality.

Therefore any initial valid state must have a FINITELY REACHABLE
valid obstruction. This is stronger proof-control information
than assuming universally that obstruction branches cannot occur.
It does NOT show the source-specific smaller-root or collision
obstructions are impossible, nor assert the required zero exit
without its explicit proof premise.
-/

namespace AllThoseRamseyClasses.Lifts

/-- In any natural-rank geometric descent, suppose the next-step
rule preserves validity, strictly decreases local B-only SOURCE
rank and conserves the exterior A-only SOURCE count. At every
positive-rank state, either an actual next step exists OR a
separately defined obstruction is visible. If all reachable
zero-rank states with the ORIGINAL exterior A-count have a
genuine terminal contradiction, then an obstruction must occur
at a valid state reachable by finitely many actual steps.

No special structure is assumed on the source carriers: this
abstract lemma is meant to consume *typed* witnesses supplied
by the concrete full-native Track C trichotomy. -/
theorem claim2_exists_reachable_obstruction_of_stepOrObstruction_and_zeroExit
    {State : Type*}
    (Valid Obstruction : State → Prop)
    (Step : State → State → Prop)
    (localBCount outsideLeftCount : State → ℕ)
    (hStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s)
    (hOutsideSame : ∀ {s t : State},
      Step s t → outsideLeftCount t = outsideLeftCount s)
    (hStepOrObstruction : ∀ s : State,
      Valid s → 0 < localBCount s →
        Obstruction s ∨ ∃ t : State, Step s t)
    {initial : State}
    (hInitial : Valid initial)
    (hZeroExit : ∀ s : State,
      Valid s →
      localBCount s = 0 →
      outsideLeftCount s = outsideLeftCount initial →
      False) :
    ∃ terminal : State,
      Valid terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      outsideLeftCount terminal = outsideLeftCount initial ∧
      Obstruction terminal := by
  let GoodStep (s t : State) : Prop :=
    Step s t ∧ ¬ Obstruction s
  have hGoodStep : ∀ {s t : State},
      Valid s → GoodStep s t →
      Valid t ∧ localBCount t < localBCount s := by
    intro s t hs hst
    exact hStep hs hst.1
  have hGoodOutside : ∀ {s t : State},
      GoodStep s t →
      outsideLeftCount t = outsideLeftCount s := by
    intro s t hst
    exact hOutsideSame hst.1
  obtain ⟨terminal, hTerminalValid, hReach, hOutside, hNoNext⟩ :=
    claim2_exists_terminal_with_constant_outsideLeft
      Valid GoodStep localBCount outsideLeftCount
      hGoodStep hGoodOutside hInitial
  have hObstruction : Obstruction terminal := by
    by_contra hNoObstruction
    rcases Nat.eq_zero_or_pos (localBCount terminal) with hz | hp
    · exact hZeroExit terminal hTerminalValid hz hOutside
    · rcases hStepOrObstruction terminal hTerminalValid hp with
        hBad | ⟨next, hNext⟩
      · exact hNoObstruction hBad
      · exact hNoNext ⟨next, hNext, hNoObstruction⟩
  have hLiftReach : ∀ {a b : State},
      Relation.ReflTransGen GoodStep a b →
        Relation.ReflTransGen Step a b := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hbc ih =>
        exact ih.trans (Relation.ReflTransGen.single hbc.1)
  have hReachStep : Relation.ReflTransGen Step initial terminal :=
    hLiftReach hReach
  exact ⟨terminal, hTerminalValid, hReachStep,
    hOutside, hObstruction⟩

end AllThoseRamseyClasses.Lifts
