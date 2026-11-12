import AllThoseRamseyClasses.Lifts.SelectedSymbolReachableProfile
import AllThoseRamseyClasses.Lifts.Claim2IteratedContextualDescent

/-!
# Track B: selected-symbol-only profile invariant along Claim 2 descent

The abstract Claim 2 finite-descent theorem keeps the valid-step rank
decrease separate from the actual existence of a flippable successor.
Here a state may have a DIFFERENT positive root width and a different
genuine selected forbidden source chart. Its single ORIGINAL global
selected symbol is enough to recover width, entire native functional
root structure, and every forbidden rooted diagram test at any reachable
terminal state.

Unlike the older four-predicate interface, no independent predicate
`ProfileFixed` or `RootWidthFixed` is needed. Target coordinates,
actual source geometry, and exterior source counts must still be encoded
in `Valid` and proved by the specific successor construction.

The result does NOT establish existence of a positive-rank successor:
its terminal condition means no `Step` successor, not automatically
B-source rank zero. The latter is an independent Track C obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A conditional finite Claim 2 descent interface which needs only
preservation of the ORIGINAL global selected symbol, not a separately
assumed width, full root or ALL-test profile invariant.

All selected state charts can have different positive widths, and
the source carrier can be encoded in each state independently.
Reachability and genuine terminality follow from strict B-source rank
descent; the complete selected SOURCE profile at the terminal follows
from transitivity of symbol equality along the ACTUAL step path and
the exact cross-width selected-symbol theorem.

The step existence and terminal exit assumptions are NOT proved here.
-/
theorem claim2_selectedSymbol_terminal_preserves_width_root_allTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    {State : Type v}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount : State → ℕ)
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
    {initial : State} (hInitial : Valid initial) :
    ∃ terminal : State,
      Valid terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      (¬ ∃ next : State, Step terminal next) ∧
      ∃ hWidth : width initial = width terminal,
        ∃ hRoot :
          (chart initial).1.root =
            (hWidth.symm ▸ chart terminal).1.root,
          (functionalDiagramPieceSetoid (chart initial).1.root F).r
            (chart initial).1.ext
            (hRoot.symm ▸ (hWidth.symm ▸ chart terminal).1.ext) := by
  have hDecrease : ∀ {s t : State}, Valid s → Step s t →
      Valid t ∧ localBCount t < localBCount s := by
    intro s t hs hst
    obtain ⟨ht, hlt, _⟩ := hStep hs hst
    exact ⟨ht, hlt⟩
  obtain ⟨terminal, hTerminal, hReach, hNoNext⟩ :=
    claim2_exists_terminal_of_strict_localB_descent
      Valid Step localBCount hDecrease hInitial
  -- One path-transport interface handles ALL reachable selected states;
  -- the terminal construction contributes only the decreasing B-rank.
  have hValidSymbolStep : ∀ {s t : State},
      Valid s → Step s t →
      Valid t ∧
      (⟨⟨width s, hWidthPos s⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width s))
          (chart s)⟩ : GlobalFunctionalPieceSymbol F) =
      ⟨⟨width t, hWidthPos t⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width t))
          (chart t)⟩ := by
    intro s t hs hst
    obtain ⟨ht, _hDrop, hSymbol⟩ := hStep hs hst
    exact ⟨ht, hSymbol⟩
  obtain ⟨_hValid, hWidth, hRoot, hTests⟩ :=
    selectedSymbol_valid_reachable_preserves_width_root_allTests
      F Valid Step width hWidthPos chart
      hValidSymbolStep hInitial hReach
  exact ⟨terminal, hTerminal, hReach, hNoNext,
    hWidth, hRoot, hTests⟩

end AllThoseRamseyClasses.Lifts
