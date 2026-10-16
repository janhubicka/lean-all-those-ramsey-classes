import AllThoseRamseyClasses.Lifts.GlobalPieceFixedRootBridge

/-!
# Transporting an equivalent global piece to one fixed functional root

The global piece quotient compares actual forbidden pieces in all
root charts at one width. Once equality of the ENTIRE native
functional root structures is known, the two pieces can be regarded
as extensions of a single root, and the global Myhill--Nerode
relation reduces to the fixed-root equivalence already used in the
verified functional flip.

This lemma manages the dependent root-equality transport explicitly.
It does not pretend that arbitrary matching arities imply equal
root structures, nor does it require global weak maps to be induced.
An independent geometric theorem constructs the nonempty forbidden
complement used to derive root equality for genuinely selected
forbidden pieces.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- Given two selected globally equivalent forbidden pieces and
EQUALITY of their whole functional roots, transfer the replacement
piece to the first chart and recover the canonical fixed-root
incompatibility equivalence. -/
theorem selectedGlobalPiece_to_fixedRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : SelectedFunctionalChart F n)
    (hroots : P.1.root = Q.1.root)
    (hEq : (globalFunctionalPieceSetoid F n).r P Q) :
    (functionalRootPieceSetoid P.1.root F).r
      P.1.ext (hroots.symm ▸ Q.1.ext) := by
  rcases P with ⟨⟨rP, eP⟩, hP⟩
  rcases Q with ⟨⟨rQ, eQ⟩, hQ⟩
  dsimp at hroots
  cases hroots
  exact (globalFunctionalPiece_equiv_iff_fixedRoot
    rP F eP eQ hP hQ).mp hEq

/-- The global equivalence class of a selected piece can be
identified with its fixed-root equivalence class once the
geometrically justified root equality has been established. -/
theorem selectedGlobalPiece_root_fixedProfile
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : SelectedFunctionalChart F n)
    (hroots : P.1.root = Q.1.root) :
    (globalFunctionalPieceSetoid F n).r P Q ↔
      (functionalRootPieceSetoid P.1.root F).r
        P.1.ext (hroots.symm ▸ Q.1.ext) := by
  rcases P with ⟨⟨rP, eP⟩, hP⟩
  rcases Q with ⟨⟨rQ, eQ⟩, hQ⟩
  dsimp at hroots
  cases hroots
  exact globalFunctionalPiece_equiv_iff_fixedRoot
    rP F eP eQ hP hQ

end AllThoseRamseyClasses.Lifts
