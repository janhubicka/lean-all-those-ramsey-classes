import AllThoseRamseyClasses.Lifts.FreeAmalgamDiagramUniqueness
import AllThoseRamseyClasses.Lifts.FreeDiagramSurjectiveTransport
import AllThoseRamseyClasses.Lifts.FunctionalDiagramFlip

/-!
# Canonical rooted gluing = existential forbidden source diagrams

This is the precise semantics bridge in Section 3, Definition
`def:incompatible`, of Hubička--Nešetřil (2019).

In the functional fixed-root language, gluing two pieces by the
canonical FULL free amalgam gives a forbidden structure up to
isomorphism if and only if some ACTUAL member of the forbidden
family is their full free amalgam with the same rooted side maps.

Forward: canonical gluing maps onto a forbidden structure via a
full embedding; transport its free diagram along this isomorphism.
Reverse: the uniqueness of full functional free-amalgam diagrams
gives a full ONTO embedding of canonical gluing into that actual
forbidden source.

NO assumption of isomorphism closure of the forbidden class is
required; membership is explicitly witnessed in the original class
on the chosen source. This applies even to nullary functions and to
set-valued function incidences. Neither direction uses the stronger
whole-fibre equality assumption for WEAK flip maps.

The resulting equivalence of root-piece incompatibility profiles
connects the previously verified canonical-rooted flip (#306) to
the actual-source diagram flip (#309), without defining a new
piece equivalence that might be weaker than the printed one.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {UR : Type v}
variable (Root : Structure L UR)

/-- Canonical forbidden root gluing and actual forbidden SOURCE
free-amalgam diagrams define exactly the same incompatibility test,
for every rooted complement Q. -/
theorem forbiddenFunctionalDiagram_iff_glue
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P Q : FunctionalRootExtension Root) :
    forbiddenFunctionalDiagram Root F P Q ↔
      forbiddenFunctionalGlue Root F P Q := by
  constructor
  · rintro ⟨W, Source, hF, iP, iQ, hfree⟩
    obtain ⟨e, hesurj, _hleft, _hright⟩ :=
      freeAmalgamDiagram_unique
        (Structure.FreeAmalgam.isFreeAmalgam
          Root P.str Q.str P.rootEmbedding Q.rootEmbedding)
        hfree
    exact ⟨W, Source, hF, e, hesurj⟩
  · rintro ⟨W, Source, hF, e, hesurj⟩
    let jP := Structure.FreeAmalgam.leftEmbedding
      Root P.str Q.str P.rootEmbedding Q.rootEmbedding
    let jQ := Structure.FreeAmalgam.rightEmbedding
      Root P.str Q.str P.rootEmbedding Q.rootEmbedding
    refine ⟨W, Source, hF, e.comp jP, e.comp jQ, ?_⟩
    exact freeAmalgamDiagram_transport_surjective
      (Structure.FreeAmalgam.isFreeAmalgam
        Root P.str Q.str P.rootEmbedding Q.rootEmbedding)
      e hesurj

/-- Equality of piece incompatibility profiles defined using
existential forbidden source diagrams is EXACTLY the manuscript's
canonical free-gluing profile equivalence (in each full functional
root chart). The test Q ranges over ALL rooted extensions. -/
theorem functionalDiagramPiece_equiv_iff_glue
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' : FunctionalRootExtension Root) :
    (functionalDiagramPieceSetoid Root F).r P P' ↔
      (functionalRootPieceSetoid Root F).r P P' := by
  constructor
  · intro h
    apply (functionalRootPiece_equiv_iff Root F P P').mpr
    intro Q
    calc
      forbiddenFunctionalGlue Root F P Q
          ↔ forbiddenFunctionalDiagram Root F P Q :=
              (forbiddenFunctionalDiagram_iff_glue Root F P Q).symm
      _ ↔ forbiddenFunctionalDiagram Root F P' Q :=
          ((functionalDiagramPiece_equiv_iff Root F P P').mp h) Q
      _ ↔ forbiddenFunctionalGlue Root F P' Q :=
          forbiddenFunctionalDiagram_iff_glue Root F P' Q
  · intro h
    apply (functionalDiagramPiece_equiv_iff Root F P P').mpr
    intro Q
    calc
      forbiddenFunctionalDiagram Root F P Q
          ↔ forbiddenFunctionalGlue Root F P Q :=
              forbiddenFunctionalDiagram_iff_glue Root F P Q
      _ ↔ forbiddenFunctionalGlue Root F P' Q :=
          ((functionalRootPiece_equiv_iff Root F P P').mp h) Q
      _ ↔ forbiddenFunctionalDiagram Root F P' Q :=
          (forbiddenFunctionalDiagram_iff_glue Root F P' Q).symm

/-- The canonical-gluing form of the FIXED-ROOT functional flip,
realized in an actual forbidden source with a complete free-amalgam
certificate and a weak EHN homomorphism-embedding to the target.

This is no longer conditional on an ad-hoc diagram profile:
its equivalence hypothesis is the manuscript's canonical gluing
incompatibility profile at this fixed, full functional root.
A separate bridge is needed to translate arbitrary root tuples
and their isomorphism charts to the paper's global piece index. -/
theorem canonicalFunctionalFlip_actualSource
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' Q : FunctionalRootExtension Root)
    (hEq : (functionalRootPieceSetoid Root F).r P P')
    (hOld : forbiddenFunctionalGlue Root F P Q)
    {UT : Type v} (Target : Structure L UT)
    (pP : P'.Carrier → UT) (pQ : Q.Carrier → UT)
    (hcompat : ∀ r,
      pP (P'.rootEmbedding r) = pQ (Q.rootEmbedding r))
    (hP : P'.str.IsEHNHomomorphismEmbedding Target pP)
    (hQ : Q.str.IsEHNHomomorphismEmbedding Target pQ) :
    ∃ (W : Type v) (Source : Structure L W),
      F Source ∧
      ∃ (iP : Structure.Embedding P'.str Source)
        (iQ : Structure.Embedding Q.str Source),
        Structure.IsFreeAmalgam P'.rootEmbedding Q.rootEmbedding iP iQ ∧
        ∃ fold : W → UT,
          Source.IsEHNHomomorphismEmbedding Target fold ∧
          (∀ a : P'.Carrier, fold (iP a) = pP a) ∧
          (∀ b : Q.Carrier, fold (iQ b) = pQ b) := by
  apply functionalDiagramFlip Root F P P' Q
    ((functionalDiagramPiece_equiv_iff_glue Root F P P').mpr hEq)
    ((forbiddenFunctionalDiagram_iff_glue Root F P Q).mpr hOld)
    Target pP pQ hcompat hP hQ

end AllThoseRamseyClasses.Lifts
