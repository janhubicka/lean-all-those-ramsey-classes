import AllThoseRamseyClasses.Lifts.Claim2TerminalLeftSupportAccounting

/-!
# The exact remaining positive-rank successor gate in Claim 2

The verified contextual finite-descent theorem already returns a
terminal valid state for any genuine local B-only SOURCE-vertex rank
which strictly decreases along every valid successor. The separately
verified terminal accounting proves an original left-support
contradiction as soon as one has a ZERO-B-rank state with:
* the original A-only anchor in the initial geometric outer piece;
* the original outer ordered root and global canonical symbol;
* injective target image of that root in the final witness;
* conserved A-only SOURCE support OUTSIDE the changing outer piece.

One still needs the MATHEMATICAL statement that EVERY positive-rank
valid state has a real next flippable B-only inner geometric piece.
This is the missing general boundary/collision successor, not a
consequence of strict decrease for a supplied step.

The two short theorems below isolate this condition sharply:

1. If all positive-rank valid states have successors, the verified
   terminal state must have rank ZERO, preserving exterior A-count
   and true finite-step reachability.
2. If every such zero-rank valid state contradicts the ORIGINAL
   left-support minimizer, no valid initial state exists.

These statements expose rather than discharge both mathematical
premises. In particular no step is postulated without showing it
in an eventual concrete instantiation, no weak EHN target map is
made injective, and no purported source-image quotient is used.

The numbered original 2019 manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

/-- Any valid finite-OUTER-PIECE B-SOURCE-rank descent with
exactly invariant A-exclusive SOURCE support outside the current
geometric piece reaches an actual terminal state of B-rank ZERO,
provided ALL positive-rank valid states have one admissible step.

A zero-rank terminal state is not presumed; it follows from
the no-successor certificate and the explicit positive-step
premise. The proof does not assume intermediate A-minimality
or a fixed source carrier type. -/
theorem claim2_exists_zeroB_terminal_with_constant_outsideLeft
    {State : Type*}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount outsideLeftCount : State → ℕ)
    (hStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s)
    (hOutsideSame : ∀ {s t : State},
      Step s t → outsideLeftCount t = outsideLeftCount s)
    (hPositiveStep : ∀ s : State,
      Valid s → 0 < localBCount s →
        ∃ t : State, Step s t)
    {initial : State}
    (hInitial : Valid initial) :
    ∃ terminal : State,
      Valid terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      localBCount terminal = 0 ∧
      outsideLeftCount terminal = outsideLeftCount initial ∧
      ¬ ∃ next : State, Step terminal next := by
  obtain ⟨terminal, hTerminalValid, hReach, hOutside, hNoNext⟩ :=
    claim2_exists_terminal_with_constant_outsideLeft
      Valid Step localBCount outsideLeftCount
      hStep hOutsideSame hInitial
  have hZero : localBCount terminal = 0 := by
    rcases Nat.eq_zero_or_pos (localBCount terminal) with hz | hp
    · exact hz
    · exact False.elim
        (hNoNext (hPositiveStep terminal hTerminalValid hp))
  exact ⟨terminal, hTerminalValid, hReach,
    hZero, hOutside, hNoNext⟩

/-- The ORIGINAL left-source-minimizer contradiction reduces to
exactly two remaining sources of mathematical proof data:
* an admissible strict B-only SOURCE-rank successor at EVERY
  positive-rank VALID geometric state;
* a genuine original-minimizer contradiction at a zero-rank
  valid state whose exterior A-exclusive SOURCE count equals
  that of the ORIGINAL state.

The terminal exit is not inferred from B-rank arithmetic
alone. The endpoint \`claim2_originalMinimizer_contradicted_by_zeroTerminalBSupport\`
of the existing library supplies the second item when the
root image injectivity and terminal full-canonical flip hypotheses
are proved from the actual common lifted witness. -/
theorem claim2_no_valid_initial_of_positiveStep_and_zeroExit
    {State : Type*}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount outsideLeftCount : State → ℕ)
    (hStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s)
    (hOutsideSame : ∀ {s t : State},
      Step s t → outsideLeftCount t = outsideLeftCount s)
    (hPositiveStep : ∀ s : State,
      Valid s → 0 < localBCount s →
        ∃ t : State, Step s t)
    {initial : State}
    (hInitial : Valid initial)
    (hZeroExit : ∀ s : State,
      Valid s →
      localBCount s = 0 →
      outsideLeftCount s = outsideLeftCount initial → False) :
    False := by
  obtain ⟨terminal, hTerminalValid, _hReach, hZero,
      hOutside, _hNoNext⟩ :=
    claim2_exists_zeroB_terminal_with_constant_outsideLeft
      Valid Step localBCount outsideLeftCount
      hStep hOutsideSame hPositiveStep hInitial
  exact hZeroExit terminal hTerminalValid hZero hOutside

end AllThoseRamseyClasses.Lifts
