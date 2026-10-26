import AllThoseRamseyClasses.Lifts.FunctionalDiagramFlip
import PartiteConstruction.Functional.FreeAmalgamReassociate

/-!
# Nested functional source diagrams and contextual profile substitution

The functional part of Claim 2 replaces a rooted sub-piece inside a
larger forbidden-source context, while retaining a second attached
rooted test. Showing that the result remains in the forbidden family
must use complete FULL native free-amalgam diagrams rather than
unjustified positive-only weak maps.

Reassociate a genuine two-step diagram

  Mid = M +_Start T,
  Ext = T +_Root Piece,
  Out = Mid +_Root Piece

into ONE genuine diagram Out = M +_Start Ext. The already verified
native functional free-amalgam reassociation theorem proves this
for ALL old relations and set-valued partial function fibres.

Consequently, if M and M' have identical forbidden functional
DIAGRAM profiles over Start, replacing M by M' in this *nested*
diagram produces an ACTUAL forbidden source M' +_Start Ext. This
is a concrete contextual use of equivalence, not an extra
"forbidden replacement available" hypothesis.

This theorem does not itself identify the resulting source's
transported OUTER context as a geometric minimal-cut piece,
or prove the full rooted outer-profile congruence for all tests:
that next bridge requires an inverse reassociation respecting
the actual embedded outer piece and its selected component.
No global injectivity of an EHN target map is assumed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A nested pair of genuine free-amalgam attachments
reassociates into a literal forbidden diagram over the
INNER original full functional root.

Unlike mere isomorphism of vertex pushout carriers, the
diagram exports the exact SAME forbidden source and
its two full embeddings with all native function fibres. -/
theorem forbiddenFunctionalDiagram_of_nestedReassociation
    (F : ∀ {W : Type}, Structure L W → Prop)
    {S M T C R P E X : Type}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R} {Piece : Structure L P}
    {Ext : Structure L E} {Out : Structure L X}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    {rT : Structure.Embedding Root Tstr}
    {rP : Structure.Embedding Root Piece}
    {jT : Structure.Embedding Tstr Ext}
    {jP : Structure.Embedding Piece Ext}
    {kMid : Structure.Embedding Mid Out}
    {kP : Structure.Embedding Piece Out}
    (hOuter : Structure.IsFreeAmalgam sM sT iM iT)
    (hExt : Structure.IsFreeAmalgam rT rP jT jP)
    (hOut : Structure.IsFreeAmalgam
      (iT.comp rT) rP kMid kP)
    (eExt : Structure.Embedding Ext Out)
    (heT : ∀ t : T, eExt (jT t) = kMid (iT t))
    (heP : ∀ p : P, eExt (jP p) = kP p)
    (hF : F Out) :
    forbiddenFunctionalDiagram Start F
      ({ Carrier := M, str := Mstr, rootEmbedding := sM } :
        FunctionalRootExtension Start)
      ({ Carrier := E, str := Ext,
         rootEmbedding := jT.comp sT } :
        FunctionalRootExtension Start) := by
  have hReassociate :
      Structure.IsFreeAmalgam
        sM (jT.comp sT) (kMid.comp iM) eExt :=
    Structure.IsFreeAmalgam.reassociate_right
      hOuter hExt hOut eExt heT heP
  exact ⟨X, Out, hF, kMid.comp iM, eExt, hReassociate⟩

/-- **Contextual use of genuine forbidden diagram equivalence.**

Starting from the ACTUAL forbidden nested source as above,
replace its inner rooted piece M by an equivalent rooted
piece M'. The existing all-tests diagram equivalence
immediately supplies another genuine forbidden source with
an exact full native free-amalgam decomposition M' +_Start Ext.

This is one direction of the rooted-context congruence that
the manuscript's iterated B-only flip requires. The theorem
does not assume or conclude any new target EHN map; the fold
and root-coordinates belong to the separate checked flip
mechanism. -/
theorem forbiddenNestedFunctionalDiagram_replaceInner
    (F : ∀ {W : Type}, Structure L W → Prop)
    {S M T C R P E X : Type}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R} {Piece : Structure L P}
    {Ext : Structure L E} {Out : Structure L X}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    {rT : Structure.Embedding Root Tstr}
    {rP : Structure.Embedding Root Piece}
    {jT : Structure.Embedding Tstr Ext}
    {jP : Structure.Embedding Piece Ext}
    {kMid : Structure.Embedding Mid Out}
    {kP : Structure.Embedding Piece Out}
    (hOuter : Structure.IsFreeAmalgam sM sT iM iT)
    (hExt : Structure.IsFreeAmalgam rT rP jT jP)
    (hOut : Structure.IsFreeAmalgam
      (iT.comp rT) rP kMid kP)
    (eExt : Structure.Embedding Ext Out)
    (heT : ∀ t : T, eExt (jT t) = kMid (iT t))
    (heP : ∀ p : P, eExt (jP p) = kP p)
    (hF : F Out)
    (Replacement : FunctionalRootExtension Start)
    (hEq : (functionalDiagramPieceSetoid Start F).r
      ({ Carrier := M, str := Mstr, rootEmbedding := sM } :
        FunctionalRootExtension Start) Replacement) :
    forbiddenFunctionalDiagram Start F Replacement
      ({ Carrier := E, str := Ext,
         rootEmbedding := jT.comp sT } :
        FunctionalRootExtension Start) := by
  exact forbiddenFunctionalDiagram_replace Start F
    ({ Carrier := M, str := Mstr, rootEmbedding := sM } :
      FunctionalRootExtension Start)
    Replacement
    ({ Carrier := E, str := Ext,
       rootEmbedding := jT.comp sT } :
      FunctionalRootExtension Start)
    hEq
    (forbiddenFunctionalDiagram_of_nestedReassociation F
      hOuter hExt hOut eExt heT heP hF)

end AllThoseRamseyClasses.Lifts
