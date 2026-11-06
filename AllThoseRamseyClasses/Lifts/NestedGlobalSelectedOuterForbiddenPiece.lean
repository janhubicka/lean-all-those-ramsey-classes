import AllThoseRamseyClasses.Lifts.NestedGeometricOuterReconstructionFromSelectedQ
import AllThoseRamseyClasses.Lifts.SelectedGeometricFlipSourceFinite
import AllThoseRamseyClasses.Lifts.SelectedReplacementInternalGeneratedRoot

/-!
# Canonical selected inner Q forces a genuine older forbidden geometric source piece

This is the end-to-end source-geometric wrapper of the two Track A
nested boundary theorems. For an actual old finite forbidden source
with two nested geometric minimal-separator pieces, suppose the
GLOBAL canonical lift selects a genuine replacement Q and supplies
a literal new forbidden source New = Q +_U originalComplement.

The selected-geometric certificate implies the full internal
generated root of a private Q component (#805), and finite Old
plus the selected Q witness imply finite New (#827). The genuine
nested reconstruction then gives an actual older geometric source
piece of New with exactly the transported old root T; because
New belongs to the forbidden family F, that rooted pattern is
also a true *forbidden geometric piece*, not an arbitrary structure.

No extra old exterior privacy, older exterior complete boundary,
new opposite boundary, new-source finiteness, or Q boundary is
assumed. The latter properties are derived from the original
nested geometry and the exact canonical selection.

This is not yet the full printed Section 3 Claim 2 support-descent:
the new older piece's ENTIRE rooted incompatibility profile has
not been identified with the full transported closed context.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type}

/-- An actual canonical selected replacement inside a nested older
geometric forbidden source yields an ACTUAL selected older
geometric forbidden piece in the new finite forbidden source.

The old and new entire roots are matched by the unchanged FULL
complement embedding. The new private source side is Q, and the
opposite side belongs to the genuinely retained complement.

No independent finiteness hypothesis for New is needed. -/
theorem nestedGeometric_globalSelectedReplacement_has_outerForbiddenPiece
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (New : Structure L W)
    (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iCompNew : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iCompNew) :
    ∃ (hFiniteNew : Finite W)
      (k : ℕ) (newOuter : GeometricFunctionalPieceData New k),
      (geometricFunctionalRootedPattern New newOuter) ∈
        forbiddenGeometricFunctionalPieces F k ∧
      Set.range newOuter.roots =
        iCompNew '' ((functionalComponentComplementEmbedding Old
          (Set.range inner.roots) inner.minimal.1 inner.left) ⁻¹'
          Set.range outer.roots) ∧
      newOuter.left.1 ∈ Set.range iCompNew ∧
      newOuter.right.1 ∈ Set.range iQ := by
  let hFiniteNew : Finite W :=
    finiteSource_of_selectedGeometricFlip
      F Old inner Q hSelected New iQ iCompNew hNewFree
  letI : Finite W := hFiniteNew
  obtain ⟨xQ, hQBoundary⟩ :=
    selectedReplacementPiece_has_internalGeneratedRoot
      F (geometricGlobalFunctionalChart Old inner).root Q hSelected
  obtain ⟨k, newOuter, hRoot, ⟨xExterior, hLeft⟩, hRight⟩ :=
    nestedGeometric_outerPiece_after_fullSelectedReplacement
      Old inner outer hNested Q New iQ iCompNew hNewFree
      xQ hQBoundary
  refine ⟨hFiniteNew, k, newOuter, ?_, hRoot, ?_, ?_⟩
  · change IsForbiddenGeometricFunctionalPiece F
      (geometricFunctionalRootedPattern New newOuter)
    exact ⟨W, New, hFiniteNew, hFNew, newOuter,
      ⟨RootedPatternIso.refl _⟩⟩
  · exact ⟨xExterior, hLeft.symm⟩
  · exact ⟨xQ.1, hRight.symm⟩

end AllThoseRamseyClasses.Lifts
