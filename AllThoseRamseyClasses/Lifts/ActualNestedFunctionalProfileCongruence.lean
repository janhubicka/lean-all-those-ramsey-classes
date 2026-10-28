import AllThoseRamseyClasses.Lifts.FunctionalNestedProfileReassociation
import AllThoseRamseyClasses.Lifts.FreeAmalgamDiagramUniqueness

/-!
# Actual forbidden-source contextual congruence of full functional diagrams

The original Section 3 Claim 2 replaces a piece inside a larger
forbidden source. It is not enough to obtain an existential new
forbidden free-amalgam diagram: an outer test has its own ACTUAL
source and is attached to a particular full functional context.

Assume the forbidden family F is invariant under an ONTO FULL
functional embedding. This is the isomorphism-invariance that is
available for an image-closed forbidden family. Two ROOTED pieces
P and P' equivalent under ALL forbidden functional diagram tests
then have the following stronger property:

If Old and New are any two ACTUAL full native free amalgams of
P +_Root Test and P' +_Root Test, respectively, then
  F Old ↔ F New.

For the forward direction, profile equivalence produces a literal
forbidden witness for P' + Test. FULL diagram uniqueness constructs
a surjective full embedding from that witness to the CHOSEN New.
Image-invariance transports its forbidden-family membership.
The other direction is symmetric. No weak-map quotient is used.

For the contextual application, if the old and new sources have
nested full native decompositions Mid = M +_Start T and
Out = Mid +_Root Piece, together with an embedded extension
Ext = T +_Root Piece, then VERIFIED native reassociation turns
each into Out = M +_Start Ext. The preceding result proves that
actual forbidden membership of the two WHOLE nested sources
is equivalent whenever M and M' have the same all-test profile.

This proves profile SUBSTITUTION in fully specified nested diagrams.
It does NOT automatically establish that the TRANSPORTED geometric
outer context is connected, rooted by a minimal separator, or
that every outside-root test of the published piece admits such
a nested diagram. Those remain separate Claim 2 obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Literal forbidden-family membership is preserved under
replacement of a rooted full functional piece by another
piece with precisely the same all-test diagram profile.

The result is for TWO CHOSEN actual source amalgams; the proof
uses full diagram uniqueness to identify the existential source
with the selected new source. -/
theorem forbiddenActualFreeDiagram_iff_of_profile_equiv
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hIso : ∀ {V W : Type}
      (A : Structure L V) (B : Structure L W)
      (e : Structure.Embedding A B),
      Function.Surjective e → F A → F B)
    {R V W : Type}
    (Root : Structure L R)
    (P P' Test : FunctionalRootExtension Root)
    (Old : Structure L V) (New : Structure L W)
    (iOldP : Structure.Embedding P.str Old)
    (iOldT : Structure.Embedding Test.str Old)
    (iNewP : Structure.Embedding P'.str New)
    (iNewT : Structure.Embedding Test.str New)
    (hOldFree : Structure.IsFreeAmalgam
      P.rootEmbedding Test.rootEmbedding iOldP iOldT)
    (hNewFree : Structure.IsFreeAmalgam
      P'.rootEmbedding Test.rootEmbedding iNewP iNewT)
    (hEq : (functionalDiagramPieceSetoid Root F).r P P') :
    F Old ↔ F New := by
  have hProfile :
      forbiddenFunctionalDiagram Root F P Test ↔
        forbiddenFunctionalDiagram Root F P' Test :=
    (functionalDiagramPiece_equiv_iff Root F P P').mp hEq Test
  constructor
  · intro hOld
    have hOldD : forbiddenFunctionalDiagram Root F P Test :=
      ⟨V, Old, hOld, iOldP, iOldT, hOldFree⟩
    obtain ⟨Z, Witness, hWit, eP, eT, hWFree⟩ :=
      hProfile.mp hOldD
    obtain ⟨e, he, _, _⟩ :=
      freeAmalgamDiagram_unique hWFree hNewFree
    exact hIso Witness New e he hWit
  · intro hNew
    have hNewD : forbiddenFunctionalDiagram Root F P' Test :=
      ⟨W, New, hNew, iNewP, iNewT, hNewFree⟩
    obtain ⟨Z, Witness, hWit, eP, eT, hWFree⟩ :=
      hProfile.mpr hNewD
    obtain ⟨e, he, _, _⟩ :=
      freeAmalgamDiagram_unique hWFree hOldFree
    exact hIso Witness Old e he hWit

/-- Contextual profile congruence for TWO actual NESTED full
functional source diagrams that share the SAME outer test
extension Ext and replace the inner root extension M by M'.

The hypotheses include the genuine nested source embeddings
and full functional free-amalgam certificates, as provided
by a valid contextual flip. They are stronger than mere
set-theoretic closure of a transported outer context. -/
theorem forbiddenNestedActualSource_iff_of_inner_profile_equiv
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hIso : ∀ {V W : Type}
      (A : Structure L V) (B : Structure L W)
      (e : Structure.Embedding A B),
      Function.Surjective e → F A → F B)
    {S M M' T C C' R P E X Y : Type}
    {Start : Structure L S}
    {Mstr : Structure L M} {M'str : Structure L M'}
    {Tstr : Structure L T}
    {OldMid : Structure L C} {NewMid : Structure L C'}
    {Root : Structure L R} {Piece : Structure L P}
    {Ext : Structure L E}
    {OldOut : Structure L X} {NewOut : Structure L Y}
    {sM : Structure.Embedding Start Mstr}
    {sM' : Structure.Embedding Start M'str}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr OldMid}
    {iT : Structure.Embedding Tstr OldMid}
    {jM : Structure.Embedding M'str NewMid}
    {jTmid : Structure.Embedding Tstr NewMid}
    {rT : Structure.Embedding Root Tstr}
    {rP : Structure.Embedding Root Piece}
    {tExt : Structure.Embedding Tstr Ext}
    {pExt : Structure.Embedding Piece Ext}
    {kOld : Structure.Embedding OldMid OldOut}
    {kNew : Structure.Embedding NewMid NewOut}
    {pOld : Structure.Embedding Piece OldOut}
    {pNew : Structure.Embedding Piece NewOut}
    (hOldMid : Structure.IsFreeAmalgam sM sT iM iT)
    (hNewMid : Structure.IsFreeAmalgam sM' sT jM jTmid)
    (hExt : Structure.IsFreeAmalgam rT rP tExt pExt)
    (hOldOut : Structure.IsFreeAmalgam
      (iT.comp rT) rP kOld pOld)
    (hNewOut : Structure.IsFreeAmalgam
      (jTmid.comp rT) rP kNew pNew)
    (eOldExt : Structure.Embedding Ext OldOut)
    (eNewExt : Structure.Embedding Ext NewOut)
    (hOldT : ∀ t : T, eOldExt (tExt t) = kOld (iT t))
    (hOldP : ∀ p : P, eOldExt (pExt p) = pOld p)
    (hNewT : ∀ t : T, eNewExt (tExt t) = kNew (jTmid t))
    (hNewP : ∀ p : P, eNewExt (pExt p) = pNew p)
    (hEq : (functionalDiagramPieceSetoid Start F).r
      ({ Carrier := M, str := Mstr, rootEmbedding := sM } :
        FunctionalRootExtension Start)
      ({ Carrier := M', str := M'str, rootEmbedding := sM' } :
        FunctionalRootExtension Start)) :
    F OldOut ↔ F NewOut := by
  have hOldRe :
      Structure.IsFreeAmalgam
        sM (tExt.comp sT) (kOld.comp iM) eOldExt :=
    Structure.IsFreeAmalgam.reassociate_right
      hOldMid hExt hOldOut eOldExt hOldT hOldP
  have hNewRe :
      Structure.IsFreeAmalgam
        sM' (tExt.comp sT) (kNew.comp jM) eNewExt :=
    Structure.IsFreeAmalgam.reassociate_right
      hNewMid hExt hNewOut eNewExt hNewT hNewP
  exact forbiddenActualFreeDiagram_iff_of_profile_equiv
    F hIso Start
    ({ Carrier := M, str := Mstr, rootEmbedding := sM } :
      FunctionalRootExtension Start)
    ({ Carrier := M', str := M'str, rootEmbedding := sM' } :
      FunctionalRootExtension Start)
    ({ Carrier := E, str := Ext,
       rootEmbedding := tExt.comp sT } :
      FunctionalRootExtension Start)
    OldOut NewOut
    (kOld.comp iM) eOldExt (kNew.comp jM) eNewExt
    hOldRe hNewRe hEq

end AllThoseRamseyClasses.Lifts
