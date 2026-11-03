import AllThoseRamseyClasses.Lifts.GeometricOuterContextProfileCongruence
import AllThoseRamseyClasses.Lifts.GeometricOuterRootRetainedFullEmbedding
import AllThoseRamseyClasses.Lifts.OldOuterGeometricContextExactCarrier
import AllThoseRamseyClasses.Lifts.EqualClosedCarrierRootedProfiles

/-!
# Original geometric piece versus actual transported context

This combines the already checked algebraic contextual congruence
with source-geometric root factorization and the exact OLD carrier.

Assume a genuine old outer geometric piece P contains the ENTIRE
inner piece (its selected component and its whole closed root),
and assume the ordered old outer root avoids the inner component.
Let the original forbidden source be cut as Inner +_U E and let
Q be ANY replacement inner full-root extension with the SAME complete
forbidden diagram incompatibility profile. Suppose a genuine new
source New = Q +_U E is provided.

Then the ORIGINAL full rooted functional piece P has EXACTLY the
same forbidden diagram profile, against ALL tests, as the ACTUAL
function-closed transported new context Q union (E intersect P).
The result also gives a full embedding of P's original ordered
root into that new context and verifies every source root coordinate.

The proof does not claim that the NEW context is a geometric piece
selected by a minimal closed separator. Track A's opposite complete
generated boundary is still needed to identify the transported
context with the new outer geometric source piece.

This result is independent of image/injective weak target maps,
forbidden-family isomorphism closure, bounded function arities,
or an ordering of the two incomparable old/inner closed roots.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual inner free source flip preserves the complete rooted
forbidden profile of the ORIGINAL old outer geometric piece on its
exact full ordered root, when the entire inner piece is contained
in that old piece and the old outer root survives on the retained
full complement side.

The newly transported context has its own genuine induced native
functional structure; it is not asserted to be a geometric piece
until a separate minimal-separator theorem is proved. -/
theorem geometricOriginalPiece_profile_equiv_transportContext
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding
      iQ iE) :
    let E := geometricGlobalComplementChart Old d
    let S := oldOuterContextInInnerComplement Old P d
    let NewK : Set W :=
      iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' S
    ∃ (hNewK : New.IsClosed NewK)
      (newRoot : Structure.Embedding
        (geometricGlobalFunctionalChart Old P).root
        (New.induce NewK hNewK)),
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old P).root F).r
        (geometricGlobalFunctionalChart Old P).ext
        ({ Carrier := NewK, str := New.induce NewK hNewK,
           rootEmbedding := newRoot } :
          FunctionalRootExtension
            (geometricGlobalFunctionalChart Old P).root) ∧
      (∀ i : Fin n,
        (newRoot i).1 =
          iE (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier)) := by
  classical
  let Inner := (geometricGlobalFunctionalChart Old d).ext
  let E := geometricGlobalComplementChart Old d
  let S := oldOuterContextInInnerComplement Old P d
  have hS : E.str.IsClosed S :=
    oldOuterContextInInnerComplement_isClosed Old P d
  let RootOuter := (geometricGlobalFunctionalChart Old P).root
  let OldPiece := (geometricGlobalFunctionalChart Old P).ext
  obtain ⟨rT, hRTval⟩ :=
    geometricOuterRoot_embedsFully_in_retainedComplement
      Old P d hOuterRootOutside
  obtain ⟨hOldK, hNewK, oldRoot, newRoot,
      hCtxProfiles, hOldCoord, hNewCoord⟩ :=
    geometricOuterContext_profile_equiv_after_innerReplacement
      F Old P d hInnerRoot Q hEq New iQ iE hFree
      RootOuter rT
  let iOldQ : Structure.Embedding Inner.str Old :=
    functionalComponentEmbedding Old (Set.range d.roots)
      d.minimal.1 d.left
  let iOldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  let OldK : Set V :=
    iOldQ '' (Set.univ : Set Inner.Carrier) ∪ iOldE '' S
  have hCarrier : OldK = geometricPieceVertices Old P :=
    geometricOldOuterContext_eq_outerPieceVertices
      Old P d hInnerRoot hInnerComponent
  have hPieceClosed : Old.IsClosed
      (geometricPieceVertices Old P) :=
    functionalComponentUnion_isClosed Old
      (Set.range P.roots) P.minimal.1 P.left
  have hRootCoordinates (i : Fin n) :
      (OldPiece.rootEmbedding i).1 = (oldRoot i).1 := by
    calc
      (OldPiece.rootEmbedding i).1 = P.roots i := rfl
      _ = (rT i).1.1 := (hRTval i).symm
      _ = iOldE ((rT i).1) := rfl
      _ = (oldRoot i).1 := (hOldCoord i).symm
  have hOldPieceProfiles :
      (functionalDiagramPieceSetoid RootOuter F).r OldPiece
        ({ Carrier := OldK, str := Old.induce OldK hOldK,
           rootEmbedding := oldRoot } : FunctionalRootExtension RootOuter) := by
    exact equalClosedCarrier_rootedProfiles_equiv
      Old (geometricPieceVertices Old P) OldK
      hPieceClosed hOldK hCarrier.symm
      RootOuter OldPiece.rootEmbedding oldRoot
      hRootCoordinates F
  have hNewProfile :
      (functionalDiagramPieceSetoid RootOuter F).r OldPiece
        ({ Carrier := _, str := New.induce _ hNewK,
           rootEmbedding := newRoot } :
          FunctionalRootExtension RootOuter) :=
    hOldPieceProfiles.trans hCtxProfiles
  refine ⟨hNewK, newRoot, hNewProfile, ?_⟩
  intro i
  calc
    (newRoot i).1 = iE ((rT i).1) := hNewCoord i
    _ = iE
        (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier) := by
      apply congrArg iE
      apply Subtype.ext
      exact hRTval i

end AllThoseRamseyClasses.Lifts
