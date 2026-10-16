import AllThoseRamseyClasses.Lifts.FunctionalFlipFold
import AllThoseRamseyClasses.Lifts.PieceEquivalence

/-!
# Fixed-root functional piece equivalence and normalized flip

A *root extension* remembers a full embedding of one chosen root
structure into a functional piece. This makes agreement of old
relations AND old function values on the ordered root explicit.

Two pieces are equivalent when they have exactly the same forbidden
free amalgams against ALL root extensions, not only against other
forbidden pieces. This is the functional version of the paper's
incompatibility equivalence, on a fixed-root chart.

Replacing a piece by an equivalent one consequently preserves
forbidden-glue membership; compatible weak (EHN) maps on its two
sides fold into one weak functional homomorphism-embedding. The
proof invokes the already certified map fold, and NEVER assumes
equality of complete function fibres for weak maps.

This theorem is the FLIP for fixed-root free-amalgam normal forms.
The remaining manuscript step is proving that every geometric
piece decomposition of a forbidden connected source is isomorphic
to such a normalized free amalgam, and coordinating different root
types and enumerations. The strong amalgamation induction is later.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {UR : Type v}
variable (Root : Structure L UR)

/-- A piece with one full, named root embedding. The carrier
may vary among extensions, but all vertices have the same universe. -/
structure FunctionalRootExtension where
  Carrier : Type v
  str : Structure L Carrier
  rootEmbedding : Structure.Embedding Root str

/-- The concrete FULL functional free amalgam of two extensions
over their identical root structure. -/
noncomputable def FunctionalRootExtension.glued
    (P Q : FunctionalRootExtension Root) :=
  Structure.FreeAmalgam.amalgam Root P.str Q.str
    P.rootEmbedding Q.rootEmbedding

/-- A glued structure is forbidden UP TO A FULL ONTO EMBEDDING,
i.e. isomorphism of functional structures. The forbidden family
need not be primitively closed under a change of vertex names. -/
def forbiddenFunctionalGlue
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P Q : FunctionalRootExtension Root) : Prop :=
  ∃ (W : Type v) (B : Structure L W),
    F B ∧ ∃ e : Structure.Embedding (FunctionalRootExtension.glued Root P Q) B,
      Function.Surjective e

/-- The entire set of complementary root extensions whose actual
functional amalgam with P is a forbidden structure (up to iso). -/
def functionalIncompatibilityProfile
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root) :
    Set (FunctionalRootExtension Root) :=
  {Q | forbiddenFunctionalGlue Root F P Q}

/-- The paper's piece equivalence in a fixed functional root chart:
all possible rooted extension tests have identical forbidden-gluing
behavior. No tests are restricted to forbidden pieces. -/
def functionalRootPieceSetoid
    (F : ∀ {W : Type v}, Structure L W → Prop) :
    Setoid (FunctionalRootExtension Root) :=
  pieceSetoid (fun P Q => forbiddenFunctionalGlue Root F P Q)

/-- A root-wise class equality is equivalent to agreement on EACH
complementary test. -/
theorem functionalRootPiece_equiv_iff
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' : FunctionalRootExtension Root) :
    (functionalRootPieceSetoid Root F).r P P' ↔
      ∀ Q, forbiddenFunctionalGlue Root F P Q ↔
        forbiddenFunctionalGlue Root F P' Q := by
  constructor
  · intro h Q
    exact incompatible_iff_of_equiv h Q
  · intro h
    exact equiv_of_incompatible_iff h

/-- Replacing a piece by an equivalent one preserves the fact
that the resulting free amalgam is forbidden, UP TO ISOMORPHISM.
This is the key semantic use of the incompatibility quotient. -/
theorem forbiddenFunctionalGlue_replace
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P P' Q : FunctionalRootExtension Root)
    (hEq : (functionalRootPieceSetoid Root F).r P P')
    (hOld : forbiddenFunctionalGlue Root F P Q) :
    forbiddenFunctionalGlue Root F P' Q :=
  ((functionalRootPiece_equiv_iff Root F P P').mp hEq Q).mp hOld

/-- Fixed-root functional flip certificate. The new source is
a member of the forbidden class UP TO ISOMORPHISM, and admits a
weak homomorphism-embedding into the chosen target extending the
two supplied weak maps.

This is stronger than merely an existential "flip can be done"
placeholder: it CONSTRUCTS the source and its folding map. It
does not assert that the new source is literally a member of a
family that is not isomorphism-closed.
-/
theorem normalizedFunctionalFlip
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
    forbiddenFunctionalGlue Root F P' Q ∧
      ∃ fold : Structure.FreeAmalgam.Vertex Root P'.str Q.str
          P'.rootEmbedding Q.rootEmbedding → UT,
        (FunctionalRootExtension.glued Root P' Q).IsEHNHomomorphismEmbedding Target fold ∧
        (∀ a : P'.Carrier,
          fold (Structure.FreeAmalgam.leftEmbedding Root P'.str Q.str
            P'.rootEmbedding Q.rootEmbedding a) = pP a) ∧
        (∀ b : Q.Carrier,
          fold (Structure.FreeAmalgam.rightEmbedding Root P'.str Q.str
            P'.rootEmbedding Q.rootEmbedding b) = pQ b) := by
  refine ⟨forbiddenFunctionalGlue_replace Root F P P' Q hEq hOld, ?_⟩
  let fold := functionalFlipFold Root P'.str Q.str
    P'.rootEmbedding Q.rootEmbedding pP pQ hcompat
  refine ⟨fold, ?_, ?_, ?_⟩
  · exact functionalFlipFold_isEHNHomomorphismEmbedding
      Root P'.str Q.str Target
      P'.rootEmbedding Q.rootEmbedding pP pQ hcompat hP hQ
  · intro a
    exact functionalFlipFold_left Root P'.str Q.str
      P'.rootEmbedding Q.rootEmbedding pP pQ hcompat a
  · intro b
    exact functionalFlipFold_right Root P'.str Q.str
      P'.rootEmbedding Q.rootEmbedding pP pQ hcompat b

end AllThoseRamseyClasses.Lifts
