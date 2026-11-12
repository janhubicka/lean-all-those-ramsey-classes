import AllThoseRamseyClasses.Lifts.Claim2SelectedSymbolDescentProfile
import AllThoseRamseyClasses.Lifts.Claim2ZeroRankTerminalGate

/-!
# Selected-symbol Claim 2 descent with exact exterior SOURCE accounting

This composes the source-side original-global-symbol invariant of Track B
with the TWO exact remaining Track C requirements: every valid positive
B-exclusive SOURCE-rank state must have an actual next admissible flip,
and a step must preserve the number of A-exclusive SOURCE vertices
outside the current genuine geometric outer piece.

The conclusion is a REACHABLE zero-B-rank terminal, unchanged exterior
A-exclusive SOURCE count, and equality of the initial/terminal full
functional root structure and EVERY forbidden native rooted diagram
test, even when the states are initially presented at different widths.

No target root-image injectivity, final left-minimizer contradiction,
general positive-rank successor, or unrestricted strong amalgamation
is inferred. No changes are made to the frozen 2019 manuscript.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Joint Track B/C conditional zero-rank terminal interface.
The original selected global symbol is the ONLY stored source-profile
invariant. Strict local B-SOURCE-rank descent, exact exterior A-SOURCE
cardinality preservation and positive-rank successor existence are
separate, explicit hypotheses. The full native root and all forbidden
diagram tests at the terminal are recovered, not postulated. -/
theorem claim2_selectedSymbol_exists_zeroB_terminal_with_exterior_and_allTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    {State : Type v}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount outsideLeftCount : State → ℕ)
    (width : State → ℕ)
    (hWidthPos : ∀ s : State, 0 < width s)
    (chart : ∀ s : State, SelectedFunctionalChart F (width s))
    (hStep : ∀ {s t : State}, Valid s → Step s t →
      Valid t ∧ localBCount t < localBCount s ∧
      (⟨⟨width s, hWidthPos s⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width s))
          (chart s)⟩ : GlobalFunctionalPieceSymbol F) =
      ⟨⟨width t, hWidthPos t⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width t))
          (chart t)⟩)
    (hOutsideSame : ∀ {s t : State},
      Step s t → outsideLeftCount t = outsideLeftCount s)
    (hPositiveStep : ∀ s : State,
      Valid s → 0 < localBCount s →
        ∃ t : State, Step s t)
    {initial : State} (hInitial : Valid initial) :
    ∃ terminal : State,
      Valid terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      localBCount terminal = 0 ∧
      outsideLeftCount terminal = outsideLeftCount initial ∧
      (¬ ∃ next : State, Step terminal next) ∧
      ∃ hWidth : width initial = width terminal,
        ∃ hRoot :
          (chart initial).1.root =
            (hWidth.symm ▸ chart terminal).1.root,
          (functionalDiagramPieceSetoid (chart initial).1.root F).r
            (chart initial).1.ext
            (hRoot.symm ▸ (hWidth.symm ▸ chart terminal).1.ext) := by
  obtain ⟨terminal, hValid, hReach, hNoNext,
      hWidth, hRoot, hTests⟩ :=
    claim2_selectedSymbol_terminal_preserves_width_root_allTests
      F Valid Step localBCount width hWidthPos chart
      hStep hInitial
  have hZero : localBCount terminal = 0 := by
    rcases Nat.eq_zero_or_pos (localBCount terminal) with hz | hp
    · exact hz
    · exact False.elim
        (hNoNext (hPositiveStep terminal hValid hp))
  have hOutsidePath :
      ∀ {a b : State}, Relation.ReflTransGen Step a b →
        outsideLeftCount b = outsideLeftCount a := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail hab hEdge ih =>
      exact (hOutsideSame hEdge).trans ih
  have hOutside : outsideLeftCount terminal =
      outsideLeftCount initial := hOutsidePath hReach
  exact ⟨terminal, hValid, hReach, hZero, hOutside,
    hNoNext, hWidth, hRoot, hTests⟩

end AllThoseRamseyClasses.Lifts
