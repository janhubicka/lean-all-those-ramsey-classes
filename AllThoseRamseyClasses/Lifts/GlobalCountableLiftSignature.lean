import AllThoseRamseyClasses.Lifts.RegularLiftPrecompactness

/-!
# Track F: countability of the ACTUAL original regular lift language

The original global distinct-root lift has one added relation symbol
for each genuine forbidden-piece incompatibility class, at each
positive width. Even for an infinite regular forbidden family, every
fixed positive-width quotient is FINITE.

The actual new relation-symbol type is a sigma of these finite fibres
over positive natural widths, and is therefore COUNTABLE. The
full lifted relation signature is the sum of the old symbols (ULifted
into the larger universe) and the piece symbols; old function symbols
are only ULifted and no new function symbol is introduced.

This gives the language-size prerequisite for Section 3's countable
Fraisse construction under a finite/countable old native signature.
It is independent of shadow avoidance, Claim 2, countability of the
finite age, and strong amalgamation. Do not identify this with the
existence of a Fraisse limit or an omega-categoricity theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u
variable {L : Language.{u}}

/-- The set of all ACTUAL global canonical piece-class relation
symbols has countable cardinality for every regular family,
even if it has unbounded root widths. -/
theorem globalFunctionalPieceSymbol_countable_of_regular
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F) :
    Countable (GlobalFunctionalPieceSymbol F) := by
  classical
  letI (k : {n : ℕ // 0 < n}) :
      Finite (GlobalFunctionalPieceClass F k.1) :=
    hRegular k.1 k.2
  infer_instance

/-- The full ORIGINAL global piece-lift relation-symbol type is
countable as soon as the original relation-symbol type is countable
and F is regular. No finite global width bound is needed. -/
theorem globalFunctionalPieceLanguage_relSymbols_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Countable L.RelSymbol]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Countable (globalFunctionalPieceLanguage F).RelSymbol := by
  letI : Countable (GlobalFunctionalPieceSymbol F) :=
    globalFunctionalPieceSymbol_countable_of_regular F hRegular
  dsimp [globalFunctionalPieceLanguage, functionalLiftLanguageBig]
  infer_instance

/-- The original global lift introduces NO additional function
symbols, so countability of native function symbols transfers
without any regularity or forbidden-family assumptions. -/
theorem globalFunctionalPieceLanguage_funcSymbols_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Countable L.FuncSymbol] :
    Countable (globalFunctionalPieceLanguage F).FuncSymbol := by
  dsimp [globalFunctionalPieceLanguage, functionalLiftLanguageBig]
  infer_instance

/-- Complete countable-signature package under finite native
symbol types and regularity of the actual forbidden family. -/
theorem globalFunctionalPieceLanguage_countable_of_finiteOld
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Countable (globalFunctionalPieceLanguage F).RelSymbol ∧
      Countable (globalFunctionalPieceLanguage F).FuncSymbol := by
  constructor
  · exact globalFunctionalPieceLanguage_relSymbols_countable
      F hRegular
  · exact globalFunctionalPieceLanguage_funcSymbols_countable F

end AllThoseRamseyClasses.Lifts
