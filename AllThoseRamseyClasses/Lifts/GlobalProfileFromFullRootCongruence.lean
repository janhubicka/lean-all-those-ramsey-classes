import AllThoseRamseyClasses.Lifts.GlobalPieceFixedRootBridge
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge

/-!
# From exact fixed-root profiles to the original GLOBAL piece quotient

The actual 2019 functional canonical lift indexes genuinely selected
forbidden geometric pieces by GLOBAL incompatibility classes at each
positive root width.  Its comparison uses full native functional
root structures, not root tuple cardinalities alone.

Once two such selected charts have literally identical full root
structures, the exact equivalence between existential full native
free-amalgam tests and canonical glued tests makes equality of ALL
fixed-root diagram profiles sufficient for equality in the GLOBAL
piece quotient, and hence equality of their added relation symbols.

This is the final quotient-transport ingredient following Track B's
actual contextual profile congruence and the separate full-root
structure-identity theorem. It does NOT itself show that the new
transported context is a genuine geometric minimal-separator piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Complete full-native fixed-root test congruence implies the
published global incompatibility equivalence between two genuinely
SELECTED forbidden pieces. Root equality is equality of the entire
functional structures on Fin n; arity equality alone is insufficient.

For different displayed roots, use a separate full-embedding root
identity theorem, never silently cast merely equal root tuples. -/
theorem selectedFunctionalChart_global_equiv_of_rootEq_and_diagram
    (F : ∀ {W : Type}, Structure L W → Prop)
    {n : ℕ}
    (P Q : SelectedFunctionalChart F n)
    (hRoot : P.1.root = Q.1.root)
    (hProfile : (functionalDiagramPieceSetoid P.1.root F).r
      P.1.ext (hRoot.symm ▸ Q.1.ext)) :
    (globalFunctionalPieceSetoid F n).r P Q := by
  rcases P with ⟨⟨Root, A⟩, hA⟩
  rcases Q with ⟨⟨Root', B⟩, hB⟩
  dsimp at hRoot
  cases hRoot
  change (functionalDiagramPieceSetoid Root F).r A B at hProfile
  exact (globalFunctionalPiece_equiv_iff_fixedRoot
    Root F A B hA hB).mpr
      ((functionalDiagramPiece_equiv_iff_glue Root F A B).mp hProfile)

/-- Equal full root structures and all-test native diagram profiles
give LITERAL equality of the published GLOBAL piece class indices.
No choice of an arbitrary representative of a quotient is involved. -/
theorem selectedFunctionalChart_global_class_eq_of_rootEq_and_diagram
    (F : ∀ {W : Type}, Structure L W → Prop)
    {n : ℕ}
    (P Q : SelectedFunctionalChart F n)
    (hRoot : P.1.root = Q.1.root)
    (hProfile : (functionalDiagramPieceSetoid P.1.root F).r
      P.1.ext (hRoot.symm ▸ Q.1.ext)) :
    (Quotient.mk (globalFunctionalPieceSetoid F n) P :
      GlobalFunctionalPieceClass F n) =
    Quotient.mk (globalFunctionalPieceSetoid F n) Q := by
  exact Quotient.sound
    (selectedFunctionalChart_global_equiv_of_rootEq_and_diagram
      F P Q hRoot hProfile)

end AllThoseRamseyClasses.Lifts
