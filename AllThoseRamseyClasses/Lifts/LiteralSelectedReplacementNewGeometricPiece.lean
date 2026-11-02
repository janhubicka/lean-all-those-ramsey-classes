import AllThoseRamseyClasses.Lifts.SelectedReplacementInternalGeneratedRoot
import AllThoseRamseyClasses.Lifts.GeometricComplementInternalBoundary
import AllThoseRamseyClasses.Lifts.TwoSidedNativeGeometricRoot

/-!
# The literal new forbidden source of a canonical flip has a genuine geometric piece

Let A be a finite original forbidden source with a GENUINE selected
geometric minimal-separator piece d, and let Q be the SAME actual
selected rooted replacement extension returned by the global 2019
canonical relation. Keep the exact old closed native complement T.
Suppose the new forbidden source New is a literal FULL functional
free amalgam Q +_Root T (as produced by the verified canonical
source flip), with both complete source embeddings.

The selected-Q witness and its full rooted geometric isomorphism
give a connected private component D_Q with
Cl_Q(N_Q(D_Q))=range(Q.rootEmbedding) (Track A #805).
The opposite original geometric component, internal to the full
unchanged complement T, has its complete root boundary as well
(Track A #809). The verified symmetric component preservation and
two-sided minimal-separator reconstruction therefore construct an
ACTUAL geometric minimal-separator piece in New whose complete
root is exactly the image of the original shared Fin n root.

The source New itself belongs to F, and the resulting rooted
geometric piece is selected for the ORIGINAL forbidden family,
not an unrelated arbitrary root extension. Its two distinguished
components arise on the inserted Q side and the unchanged old
complement side, respectively.

No weak target-map injectivity, graph-induced-substructure
shortcut, or changed forbidden family is used. This establishes
the new INNER geometric source witness; preserving an OLDER
outer nested geometric piece and its entire incompatibility
profile remains a separate Track A/B/C obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A finite LITERAL canonical replacement full-functional source
amalgam has a genuine selected forbidden geometric piece with
the exactly transported full root, provided Q is the exact
genuinely selected replacement from the global piece relation.

This theorem does NOT assume either private-side generated-boundary
equation: both follow from the selected geometric witness and
the original genuine opposite component. It does assume the
literal free-amalgam source and its forbidden-family membership,
which the existing global canonical flip already exports. -/
theorem literalSelectedReplacement_has_newGeometricPiece
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type} [Finite W]
    (A : Structure L V)
    (d : GeometricFunctionalPieceData A n)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart A d).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart A d).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (New : Structure L W) (hNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iT : Structure.Embedding (geometricGlobalComplementChart A d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding (geometricGlobalComplementChart A d).rootEmbedding
        iQ iT) :
    ∃ (m : ℕ) (dNew : GeometricFunctionalPieceData New m),
      (geometricFunctionalRootedPattern New dNew) ∈
        forbiddenGeometricFunctionalPieces F m ∧
      Set.range dNew.roots =
        iT '' Set.range (geometricGlobalComplementChart A d).rootEmbedding ∧
      dNew.left.1 ∈ Set.range iQ ∧
      dNew.right.1 ∈ Set.range iT := by
  obtain ⟨xQ, hQBoundary⟩ :=
    selectedReplacementPiece_has_internalGeneratedRoot
      F (geometricGlobalFunctionalChart A d).root Q hSelected
  obtain ⟨xT, hTBoundary⟩ :=
    geometricGlobalComplement_internalBoundary_eq_root A d
  obtain ⟨m, dNew, hRoot, hLeft, hRight⟩ :=
    fullFreeAmalgam_twoPrivateBoundaries_hasGeometricPiece
      hFree xQ xT hQBoundary hTBoundary
  refine ⟨m, dNew, ?_, hRoot, ?_, ?_⟩
  · change IsForbiddenGeometricFunctionalPiece F
      (geometricFunctionalRootedPattern New dNew)
    exact ⟨W, New, inferInstance, hNew, dNew,
      ⟨RootedPatternIso.refl _⟩⟩
  · exact ⟨xQ.1, hLeft.symm⟩
  · exact ⟨xT.1, hRight.symm⟩

end AllThoseRamseyClasses.Lifts
