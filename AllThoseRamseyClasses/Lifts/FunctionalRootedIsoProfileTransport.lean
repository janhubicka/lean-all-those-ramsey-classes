import AllThoseRamseyClasses.Lifts.FreeAmalgamSideIso
import AllThoseRamseyClasses.Lifts.FunctionalDiagramFlip

/-!
# Native forbidden test profiles are invariant under rooted FULL isomorphism

The inner-stage restriction in the contextual Claim 2 argument
naturally constructs a full source `M +_S T` on a new induced
subtype carrier, whereas the original geometric outer context
has its own carrier.  Actual full free-amalgam diagrams of the
same sides are isomorphic, but identifying these outer contexts
requires an explicit rooted FULL-isomorphism profile transport.

This file proves that any onto full native functional embedding
respecting the entire common root preserves the forbidden gluing
answer for EVERY rooted test, and hence the complete fixed-root
piece equivalence class.

No isomorphism-closure assumption on the forbidden family is used:
the full source W of each forbidden test is literally unchanged,
only the named embedded side is reparameterized.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Both directions of native rooted test preservation are witnessed
by the SAME forbidden whole source, after replacing one diagram side
by an onto FULL rooted embedding or its full inverse. -/
theorem forbiddenFunctionalDiagram_iff_of_ontoRootIso
    {R : Type}
    (Root : Structure L R)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P P' : FunctionalRootExtension Root)
    (e : Structure.Embedding P.str P'.str)
    (he : Function.Surjective e)
    (hroot : ∀ r : R, e (P.rootEmbedding r) = P'.rootEmbedding r)
    (Test : FunctionalRootExtension Root) :
    forbiddenFunctionalDiagram Root F P Test ↔
      forbiddenFunctionalDiagram Root F P' Test := by
  constructor
  · rintro ⟨W, Whole, hForbidden, iP, iTest, hFree⟩
    let g : Structure.Embedding P'.str P.str :=
      inverseFullEmbedding e he
    have hgsurj : Function.Surjective g := by
      intro p
      exact ⟨e p, inverseFullEmbedding_left e he p⟩
    have hgroot : ∀ r : R,
        g (P'.rootEmbedding r) = P.rootEmbedding r := by
      intro r
      apply e.injective
      calc
        e (g (P'.rootEmbedding r)) = P'.rootEmbedding r :=
          inverseFullEmbedding_right e he (P'.rootEmbedding r)
        _ = e (P.rootEmbedding r) := (hroot r).symm
    exact ⟨W, Whole, hForbidden, iP.comp g, iTest,
      freeAmalgam_precompose_left_iso
        hFree g hgsurj P'.rootEmbedding hgroot⟩
  · rintro ⟨W, Whole, hForbidden, iP', iTest, hFree⟩
    exact ⟨W, Whole, hForbidden, iP'.comp e, iTest,
      freeAmalgam_precompose_left_iso
        hFree e he P.rootEmbedding hroot⟩

/-- Full rooted isomorphism is sufficient for equality of the
ENTIRE native incompatibility profile (all rooted test extensions);
no target EHN weak-map injectivity, finite carriers or class
isomorphism invariance hypothesis is needed. -/
theorem functionalDiagramPiece_equiv_of_ontoRootIso
    {R : Type}
    (Root : Structure L R)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P P' : FunctionalRootExtension Root)
    (e : Structure.Embedding P.str P'.str)
    (he : Function.Surjective e)
    (hroot : ∀ r : R, e (P.rootEmbedding r) = P'.rootEmbedding r) :
    (functionalDiagramPieceSetoid Root F).r P P' := by
  apply (functionalDiagramPiece_equiv_iff Root F P P').mpr
  intro Test
  exact forbiddenFunctionalDiagram_iff_of_ontoRootIso
    Root F P P' e he hroot Test

end AllThoseRamseyClasses.Lifts
