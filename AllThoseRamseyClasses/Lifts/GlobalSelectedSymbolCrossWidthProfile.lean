import AllThoseRamseyClasses.Lifts.GlobalSelectedSymbolProfileEquivalence

/-!
# The original 2019 global selected symbol fixes its root width as well as its profile

For genuinely selected pieces, the fixed-positive-width theorem already
identifies equality of global Myhill--Nerode symbols with equality of
their complete functional root structures and all full rooted native
forbidden-diagram tests.

A Claim 2 state may initially be presented with a varying number of
root coordinates. Equality of the ORIGINAL *dependent* global symbols
already forces those widths to agree. We make the dependent transport
explicit; no equal-width oracle is hidden in the conclusion.

This statement concerns genuine selected SOURCE pieces. It says nothing
about injectivity of their images under weak maps into a TARGET.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Even if two genuinely selected pieces are presented at DIFFERENT
positive root widths, equality of their ORIGINAL dependent global
symbols is equivalent to the existence of an equality of widths and
(with the second chart transported across it) equality of complete
functional roots and of ALL forbidden native full-diagram tests.

In particular, a separately maintained `RootWidthFixed` invariant
is redundant whenever the actual selected global symbol is fixed. -/
theorem selectedFunctionalChart_globalSymbol_eq_iff_width_root_allTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (P : SelectedFunctionalChart F n)
    (Q : SelectedFunctionalChart F m) :
    (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n) P⟩ :
        GlobalFunctionalPieceSymbol F) =
      ⟨⟨m, hm⟩, Quotient.mk (globalFunctionalPieceSetoid F m) Q⟩ ↔
    ∃ hWidth : n = m,
      ∃ hRoot : P.1.root = (hWidth.symm ▸ Q).1.root,
        (functionalDiagramPieceSetoid P.1.root F).r
          P.1.ext (hRoot.symm ▸ (hWidth.symm ▸ Q).1.ext) := by
  constructor
  · intro hSymbol
    have hWidthTag :
        (⟨n, hn⟩ : {k : ℕ // 0 < k}) =
          (⟨m, hm⟩ : {k : ℕ // 0 < k}) :=
      congrArg Sigma.fst hSymbol
    have hWidth : n = m := congrArg Subtype.val hWidthTag
    cases hWidth
    have hProof : hn = hm := Subsingleton.elim _ _
    cases hProof
    obtain ⟨hRoot, hTests⟩ :=
      (selectedFunctionalChart_globalSymbol_eq_iff_rootEq_and_diagram
        F hn P Q).mp hSymbol
    exact ⟨rfl, hRoot, hTests⟩
  · rintro ⟨hWidth, hRoot, hTests⟩
    cases hWidth
    have hProof : hn = hm := Subsingleton.elim _ _
    cases hProof
    exact (selectedFunctionalChart_globalSymbol_eq_iff_rootEq_and_diagram
      F hn P Q).mpr ⟨hRoot, hTests⟩

/-- A changing-width version directly for ACTUAL finite forbidden
geometric source pieces. Full ordered roots and all forbidden source
tests are compared after transporting the second selected chart across
the width equality FORCED by the global symbol. -/
theorem geometricGlobalPieceSymbol_eq_iff_width_root_allTests
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type}
    (Old : Structure L V) (hFiniteOld : Finite V) (hOld : F Old)
    (New : Structure L W) (hFiniteNew : Finite W) (hNew : F New)
    {n m : ℕ}
    (oldPiece : GeometricFunctionalPieceData Old n)
    (newPiece : GeometricFunctionalPieceData New m)
    (hn : 0 < n) (hm : 0 < m) :
    geometricGlobalPieceSymbol F Old hFiniteOld hOld oldPiece hn =
      geometricGlobalPieceSymbol F New hFiniteNew hNew newPiece hm ↔
    ∃ hWidth : n = m,
      ∃ hRoot :
          (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece).1.root =
            (hWidth.symm ▸
              geometricGlobalSelectedChart F New hFiniteNew hNew newPiece).1.root,
        (functionalDiagramPieceSetoid
          (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece).1.root F).r
            (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece).1.ext
            (hRoot.symm ▸
              (hWidth.symm ▸
                geometricGlobalSelectedChart F New hFiniteNew hNew newPiece).1.ext) := by
  change
    (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
      (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece)⟩ :
      GlobalFunctionalPieceSymbol F) =
      ⟨⟨m, hm⟩, Quotient.mk (globalFunctionalPieceSetoid F m)
        (geometricGlobalSelectedChart F New hFiniteNew hNew newPiece)⟩ ↔ _
  exact selectedFunctionalChart_globalSymbol_eq_iff_width_root_allTests
    F hn hm
      (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece)
      (geometricGlobalSelectedChart F New hFiniteNew hNew newPiece)

end AllThoseRamseyClasses.Lifts
