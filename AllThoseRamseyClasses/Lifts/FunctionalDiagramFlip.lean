import AllThoseRamseyClasses.Lifts.ArbitraryFunctionalFreeFold
import AllThoseRamseyClasses.Lifts.NormalizedFunctionalFlip

/-!
# Flip in an actual forbidden functional source diagram

This is the proof-oriented version of the paper's Section 3 flip:
a forbidden SOURCE may already be presented as a full functional free
amalgam over a closed root, without first identifying its carrier
with the library's particular canonical amalgam.

For a fixed full functional root R, two root extensions P and P'
are diagram-equivalent when they give forbidden full free amalgams
with exactly the same complementary rooted extensions Q.

If P⊕Q has a forbidden free source witness, equivalence provides
a full forbidden free source for P'⊕Q. The verified arbitrary-source
compatible fold then constructs the target weak homomorphism-
embedding with exactly the specified restrictions to P' and Q.

The missing manuscript bridge is to identify its rooted
incompatibility relation (canonical gluing up to isomorphism)
with this existential diagram relation, and to represent all
geometric minimal-cut pieces as root extensions in these fixed
root charts. No assertion of the final strong amalgamation
minimal-support induction is included.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {UR : Type v}
variable (Root : Structure L UR)

/-- A forbidden SOURCE which is a genuine functional free amalgam
of P and Q over their common full functional root. No particular
implementation of the amalgam carrier is assumed. -/
def forbiddenFunctionalDiagram
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P Q : FunctionalRootExtension Root) : Prop :=
  ∃ (W : Type v) (Source : Structure L W),
    F Source ∧
    ∃ (iP : Structure.Embedding P.str Source)
      (iQ : Structure.Embedding Q.str Source),
      Structure.IsFreeAmalgam P.rootEmbedding Q.rootEmbedding iP iQ

/-- The set of all rooted complementary tests against which P
produces an actual forbidden full functional source diagram. -/
def forbiddenFunctionalDiagramProfile
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root) :
    Set (FunctionalRootExtension Root) :=
  {Q | forbiddenFunctionalDiagram Root F P Q}

/-- Equivalence by the SAME forbidden diagrams with every possible
complementary rooted extension. Do not restrict tests to forbidden
pieces, since this would change the equivalence. -/
def functionalDiagramPieceSetoid
    (F : ∀ {W : Type v}, Structure L W → Prop) :
    Setoid (FunctionalRootExtension Root) :=
  pieceSetoid (fun P Q => forbiddenFunctionalDiagram Root F P Q)

/-- Diagram equivalence is exactly agreement of all rooted
compatibility tests. -/
theorem functionalDiagramPiece_equiv_iff
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' : FunctionalRootExtension Root) :
    (functionalDiagramPieceSetoid Root F).r P P' ↔
      ∀ Q, forbiddenFunctionalDiagram Root F P Q ↔
        forbiddenFunctionalDiagram Root F P' Q := by
  constructor
  · intro h Q
    exact incompatible_iff_of_equiv h Q
  · intro h
    exact equiv_of_incompatible_iff h

/-- Equivalent pieces give a forbidden REPLACEMENT SOURCE diagram
whenever the original actual source was forbidden. -/
theorem forbiddenFunctionalDiagram_replace
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' Q : FunctionalRootExtension Root)
    (hEq : (functionalDiagramPieceSetoid Root F).r P P')
    (hOld : forbiddenFunctionalDiagram Root F P Q) :
    forbiddenFunctionalDiagram Root F P' Q :=
  ((functionalDiagramPiece_equiv_iff Root F P P').mp hEq Q).mp hOld

/-- A FULL fixed-root diagram flip: the output is an actual forbidden
source together with its free amalgam embeddings and a constructed
WEAK map into the target. The new map agrees with the old map on
the complement Q and with its new rooted-piece map on P'.

The original source and the replacement source need not have the
same carrier, and maps on the two sides may collide away from R.
-/
theorem functionalDiagramFlip
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' Q : FunctionalRootExtension Root)
    (hEq : (functionalDiagramPieceSetoid Root F).r P P')
    (hOld : forbiddenFunctionalDiagram Root F P Q)
    {UT : Type v} (Target : Structure L UT)
    (pP : P'.Carrier → UT) (pQ : Q.Carrier → UT)
    (hcompat : ∀ r, pP (P'.rootEmbedding r) = pQ (Q.rootEmbedding r))
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
  obtain ⟨W, Source, hSource, iP, iQ, hfree⟩ :=
    forbiddenFunctionalDiagram_replace Root F P P' Q hEq hOld
  let fold : W → UT := compatibleFunctionalFold hfree pP pQ hcompat
  refine ⟨W, Source, hSource, iP, iQ, hfree, fold, ?_, ?_, ?_⟩
  · exact compatibleFunctionalFold_isEHNHomomorphismEmbedding
      hfree pP pQ hcompat hP hQ
  · intro a
    exact compatibleFunctionalFold_left hfree pP pQ hcompat a
  · intro b
    exact compatibleFunctionalFold_right hfree pP pQ hcompat b

end AllThoseRamseyClasses.Lifts
