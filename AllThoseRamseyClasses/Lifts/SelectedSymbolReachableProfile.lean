import AllThoseRamseyClasses.Lifts.GlobalSelectedSymbolCrossWidthProfile

/-!
# Track B: source profile transport across any actual finite sequence of selected steps

The original 2019 global selected symbol fixes the entire full native
functional root structure, including every function fibre, and the
incompatibility relation with EVERY forbidden rooted diagram test.

Unlike the existing terminal-only Claim 2 wrapper, these two theorems
extract that source-side information at an ARBITRARY reachable state.
There is no finite-rank descent, root-width equality, terminality or
positive-rank successor existence premise.

For concrete selected-Q geometric steps, use the second theorem with
`Valid` carrying the actual forbidden source, positive geometric piece,
target coordinates, exterior SOURCE counts and other side conditions.
These are NOT consequences of source-symbol equality.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A finite path of genuine selected-source steps preserving the ORIGINAL
global 2019 canonical symbol automatically preserves its positive root
width, complete native full functional root and ALL forbidden diagram
tests. This is purely source-side: the weak TARGET root images may still
collide. No rank or terminal premise is needed. -/
theorem selectedSymbol_reachable_preserves_width_root_allTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    {State : Type v}
    (Step : State → State → Prop)
    (width : State → ℕ)
    (hWidthPos : ∀ s : State, 0 < width s)
    (chart : ∀ s : State, SelectedFunctionalChart F (width s))
    (hStepSymbol : ∀ {s t : State}, Step s t →
      (⟨⟨width s, hWidthPos s⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width s))
          (chart s)⟩ : GlobalFunctionalPieceSymbol F) =
      ⟨⟨width t, hWidthPos t⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width t))
          (chart t)⟩)
    {start finish : State}
    (hReach : Relation.ReflTransGen Step start finish) :
    ∃ hWidth : width start = width finish,
      ∃ hRoot : (chart start).1.root =
          (hWidth.symm ▸ chart finish).1.root,
        (functionalDiagramPieceSetoid (chart start).1.root F).r
          (chart start).1.ext
          (hRoot.symm ▸ (hWidth.symm ▸ chart finish).1.ext) := by
  let symbol : State → GlobalFunctionalPieceSymbol F := fun s =>
    ⟨⟨width s, hWidthPos s⟩,
      Quotient.mk (globalFunctionalPieceSetoid F (width s))
        (chart s)⟩
  have hAlong : ∀ {a b : State},
      Relation.ReflTransGen Step a b → symbol a = symbol b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail hab hEdge ih =>
        exact ih.trans (hStepSymbol hEdge)
  exact (selectedFunctionalChart_globalSymbol_eq_iff_width_root_allTests
    F (hWidthPos start) (hWidthPos finish)
    (chart start) (chart finish)).mp (hAlong hReach)

/-- The valid-state form: no global invariant is assumed outside valid
states. Steps must preserve validity and the original selected global
symbol, and the starting state must be valid. Every finitely reachable
state is valid and carries the complete original source profile.

No existence of a next move, source-rank decrease, exterior count or
target tuple injectivity is inferred. -/
theorem selectedSymbol_valid_reachable_preserves_width_root_allTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    {State : Type v}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (width : State → ℕ)
    (hWidthPos : ∀ s : State, 0 < width s)
    (chart : ∀ s : State, SelectedFunctionalChart F (width s))
    (hStep : ∀ {s t : State}, Valid s → Step s t →
      Valid t ∧
      (⟨⟨width s, hWidthPos s⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width s))
          (chart s)⟩ : GlobalFunctionalPieceSymbol F) =
      ⟨⟨width t, hWidthPos t⟩,
        Quotient.mk (globalFunctionalPieceSetoid F (width t))
          (chart t)⟩)
    {start finish : State}
    (hStart : Valid start)
    (hReach : Relation.ReflTransGen Step start finish) :
    Valid finish ∧
      ∃ hWidth : width start = width finish,
        ∃ hRoot : (chart start).1.root =
            (hWidth.symm ▸ chart finish).1.root,
          (functionalDiagramPieceSetoid (chart start).1.root F).r
            (chart start).1.ext
            (hRoot.symm ▸ (hWidth.symm ▸ chart finish).1.ext) := by
  let symbol : State → GlobalFunctionalPieceSymbol F := fun s =>
    ⟨⟨width s, hWidthPos s⟩,
      Quotient.mk (globalFunctionalPieceSetoid F (width s))
        (chart s)⟩
  have hAlong : ∀ {a b : State},
      Relation.ReflTransGen Step a b →
        ∀ ha : Valid a, Valid b ∧ symbol a = symbol b := by
    intro a b hab
    induction hab with
    | refl =>
        intro ha
        exact ⟨ha, rfl⟩
    | tail hab hEdge ih =>
        intro ha
        obtain ⟨hMid, hSame⟩ := ih ha
        obtain ⟨hEnd, hStepEq⟩ := hStep hMid hEdge
        exact ⟨hEnd, hSame.trans hStepEq⟩
  obtain ⟨hFinish, hSymbol⟩ := hAlong hReach hStart
  exact ⟨hFinish,
    (selectedFunctionalChart_globalSymbol_eq_iff_width_root_allTests
      F (hWidthPos start) (hWidthPos finish)
      (chart start) (chart finish)).mp hSymbol⟩

end AllThoseRamseyClasses.Lifts
