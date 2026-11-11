import AllThoseRamseyClasses.Lifts.GlobalProfileFromFullRootCongruence
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# Exact selected GLOBAL symbol ↔ complete native root and all-test profile

A selected 2019 forbidden piece always has a genuine forbidden complement
test. Consequently the global Myhill--Nerode CLASS determines the whole
functional root structure and complete incompatibility profile. This file
also transports that equivalence to the actual width-indexed GLOBAL
canonical symbol, where both classes occur in the same positive width
fibre of the dependent symbol type.

No arbitrary unselected chart is claimed to have a nonempty profile.
This is a source-level statement, NOT a weak target-map embedding result,
and does not prove the positive-rank successor or terminal Claim 2 step.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- At a fixed positive root width, equality of original GLOBAL
canonical relation *symbols* for two genuinely selected finite
forbidden pieces is equivalent to equality of their FULL ordered
functional roots and ALL full native forbidden amalgamation tests.

The forward direction is NOT valid without selected-piece nonempty
profiles. No image/isomorphism closure of F or weak target-map root
injectivity is used. -/
theorem selectedFunctionalChart_globalSymbol_eq_iff_rootEq_and_diagram
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {n : ℕ} (hn : 0 < n)
    (P Q : SelectedFunctionalChart F n) :
    (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n) P⟩ :
        GlobalFunctionalPieceSymbol F) =
      ⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n) Q⟩ ↔
    ∃ (hRoot : P.1.root = Q.1.root),
      (functionalDiagramPieceSetoid P.1.root F).r
        P.1.ext (hRoot.symm ▸ Q.1.ext) := by
  constructor
  · intro hSymbol
    have hHClass :
        HEq (Quotient.mk (globalFunctionalPieceSetoid F n) P :
          GlobalFunctionalPieceClass F n)
          (Quotient.mk (globalFunctionalPieceSetoid F n) Q :
            GlobalFunctionalPieceClass F n) :=
      (Sigma.mk.inj_iff.mp hSymbol).2
    have hClass :
        (Quotient.mk (globalFunctionalPieceSetoid F n) P :
          GlobalFunctionalPieceClass F n) =
        Quotient.mk (globalFunctionalPieceSetoid F n) Q :=
      eq_of_heq hHClass
    exact (selectedFunctionalChart_global_class_eq_iff_rootEq_and_diagram
      F P Q).mp hClass
  · intro hProfile
    have hClass :
        (Quotient.mk (globalFunctionalPieceSetoid F n) P :
          GlobalFunctionalPieceClass F n) =
        Quotient.mk (globalFunctionalPieceSetoid F n) Q :=
      (selectedFunctionalChart_global_class_eq_iff_rootEq_and_diagram
        F P Q).mpr hProfile
    exact congrArg
      (fun cls : GlobalFunctionalPieceClass F n =>
        (⟨⟨n, hn⟩, cls⟩ : GlobalFunctionalPieceSymbol F))
      hClass

/-- For ACTUAL finite forbidden geometric source pieces, equality of
their original GLOBAL 2019 relation symbol is *exactly* preservation
of the entire ordered native functional root and the complete set
of forbidden full source diagram tests. This is the invariant
normalization used by the Claim 2 iterative argument. -/
theorem geometricGlobalPieceSymbol_eq_iff_fullRoot_allTests
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type}
    (Old : Structure L V) (hFiniteOld : Finite V) (hOld : F Old)
    (New : Structure L W) (hFiniteNew : Finite W) (hNew : F New)
    {n : ℕ}
    (oldPiece : GeometricFunctionalPieceData Old n)
    (newPiece : GeometricFunctionalPieceData New n)
    (hn : 0 < n) :
    geometricGlobalPieceSymbol F Old hFiniteOld hOld oldPiece hn =
      geometricGlobalPieceSymbol F New hFiniteNew hNew newPiece hn ↔
    ∃ (hRoot :
        (geometricGlobalFunctionalChart Old oldPiece).root =
          (geometricGlobalFunctionalChart New newPiece).root),
      (functionalDiagramPieceSetoid
          (geometricGlobalFunctionalChart Old oldPiece).root F).r
        (geometricGlobalFunctionalChart Old oldPiece).ext
        (hRoot.symm ▸ (geometricGlobalFunctionalChart New newPiece).ext) := by
  change
    (⟨⟨n, hn⟩,
      Quotient.mk (globalFunctionalPieceSetoid F n)
        (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece)⟩ :
        GlobalFunctionalPieceSymbol F) =
      ⟨⟨n, hn⟩,
        Quotient.mk (globalFunctionalPieceSetoid F n)
          (geometricGlobalSelectedChart F New hFiniteNew hNew newPiece)⟩ ↔ _
  exact selectedFunctionalChart_globalSymbol_eq_iff_rootEq_and_diagram
    F hn
    (geometricGlobalSelectedChart F Old hFiniteOld hOld oldPiece)
    (geometricGlobalSelectedChart F New hFiniteNew hNew newPiece)

end AllThoseRamseyClasses.Lifts
