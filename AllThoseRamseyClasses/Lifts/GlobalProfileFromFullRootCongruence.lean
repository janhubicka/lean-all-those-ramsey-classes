import AllThoseRamseyClasses.Lifts.GlobalPieceFixedRootBridge
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge
import AllThoseRamseyClasses.Lifts.SelectedGlobalPieceFixedRoot
import AllThoseRamseyClasses.Lifts.ForbiddenPieceProfileNonempty

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


/-- **Exact converse of the global-quotient transport theorem.**

For genuinely selected finite forbidden pieces of the same root width,
equality of their ORIGINAL 2019 global Myhill--Nerode quotient classes
is equivalent to equality of the **entire** ordered native functional
root structures, together with equivalence against EVERY full rooted
forbidden source-gluing test.

The forward direction depends on the genuine selected-piece
nonempty-complement theorem: equality of two empty global profiles
would NOT determine their root structures for arbitrary unselected
rooted charts. No isomorphism-closure assumption on F is added.

In a Claim 2 iteration, this lets the invariant "global selected
piece symbol fixed" recover the whole full-rooted all-test profile;
the source root coordinates and target-map accounting remain
separate invariants. -/
theorem selectedFunctionalChart_global_class_eq_iff_rootEq_and_diagram
    (F : ∀ {W : Type}, Structure L W → Prop)
    {n : ℕ}
    (P Q : SelectedFunctionalChart F n) :
    (Quotient.mk (globalFunctionalPieceSetoid F n) P :
        GlobalFunctionalPieceClass F n) =
      Quotient.mk (globalFunctionalPieceSetoid F n) Q ↔
    ∃ (hRoot : P.1.root = Q.1.root),
      (functionalDiagramPieceSetoid P.1.root F).r
        P.1.ext (hRoot.symm ▸ Q.1.ext) := by
  constructor
  · intro hClass
    have hGlobal : (globalFunctionalPieceSetoid F n).r P Q :=
      Quotient.exact hClass
    have hRoot : P.1.root = Q.1.root :=
      globalFunctionalPiece_equiv_root_eq F P Q hGlobal
    have hFixed : (functionalRootPieceSetoid P.1.root F).r
        P.1.ext (hRoot.symm ▸ Q.1.ext) :=
      selectedGlobalPiece_to_fixedRoot F P Q hRoot hGlobal
    exact ⟨hRoot,
      (functionalDiagramPiece_equiv_iff_glue
        P.1.root F P.1.ext (hRoot.symm ▸ Q.1.ext)).mpr hFixed⟩
  · rintro ⟨hRoot, hProfile⟩
    exact selectedFunctionalChart_global_class_eq_of_rootEq_and_diagram
      F P Q hRoot hProfile

end AllThoseRamseyClasses.Lifts
