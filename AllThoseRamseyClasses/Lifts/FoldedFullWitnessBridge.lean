import AllThoseRamseyClasses.Lifts.FoldedCommonGlobalDiagramFlip

/-!
# Two full embeddings of the SAME folded lift give the common witness diagram

The paper's maximal-lift witnesses do not merely share the old
functional shadow X: they each induce an expansion of the SAME
finite lifted structure. The common-full-lift interface used by
the folded piece flip is therefore available directly from the
two induced full expanded embeddings.

This module proves the exact faithful-language conversion:
  a full embedding LiftX -> L_fold(A) induces a full embedding
  of the ORIGINAL relation/function shadow X -> A with the SAME
  underlying vertex map, and two such embeddings of the SAME LiftX
  supply all fields of CommonFoldedGlobalCanonicalLift.

The existence of a maximal-folded-lift witness in the larger class
remains a separate class-level task. But once two witnesses induce
the SAME folded expansion, there is no additional 'common lift'
oracle. Old function fibres and domains are preserved exactly.
No root-image injectivity is required.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A FULL embedding of a given folded lifted structure into the
auxiliary canonical folded lift of its witness induces an exact
original functional shadow embedding with the SAME vertex map.
The entire original function-value fibres are reflected. -/
def foldedFullWitness_shadowEmbedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    (LiftX : Structure (globalFunctionalPieceLanguage F) UX)
    (A : Structure L UA)
    (e : Structure.Embedding LiftX (foldedGlobalCanonicalLift F A)) :
    Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) LiftX)
      A := by
  have h : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) LiftX)
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F)
        (foldedGlobalCanonicalLift F A)) :=
    functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) e
  simpa only [foldedGlobalCanonicalLift_shadow] using h

/-- The original and lifted maps constructed above coincide on
EVERY vertex, not just on designated roots. -/
theorem foldedFullWitness_shadowEmbedding_apply
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    (LiftX : Structure (globalFunctionalPieceLanguage F) UX)
    (A : Structure L UA)
    (e : Structure.Embedding LiftX (foldedGlobalCanonicalLift F A))
    (x : UX) :
    foldedFullWitness_shadowEmbedding F LiftX A e x = e x := by
  rfl

/-- Two full embeddings of the SAME auxiliary folded expansion
into two canonical folded witnesses automatically give precisely
the common-full-lift diagram used by the verified
collision-tolerant forbidden-piece flip.

No independent equality of piece relation predicates and no
manually supplied old root embeddings are needed. -/
def commonFoldedFullLift_of_sharedExpansion
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (LiftX : Structure (globalFunctionalPieceLanguage F) UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (eLeft : Structure.Embedding LiftX
      (foldedGlobalCanonicalLift F Left))
    (eRight : Structure.Embedding LiftX
      (foldedGlobalCanonicalLift F Right)) :
    CommonFoldedGlobalCanonicalLift F
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) LiftX)
      Left Right
      (foldedFullWitness_shadowEmbedding F LiftX Left eLeft)
      (foldedFullWitness_shadowEmbedding F LiftX Right eRight) where
  lifted := LiftX
  shadow_eq := rfl
  intoLeft := eLeft
  intoRight := eRight
  intoLeft_verts := fun x =>
    (foldedFullWitness_shadowEmbedding_apply
      F LiftX Left eLeft x).symm
  intoRight_verts := fun x =>
    (foldedFullWitness_shadowEmbedding_apply
      F LiftX Right eRight x).symm

/-- Full induced embeddings of one shared folded lift imply that
EVERY folded global piece relation agrees on its original-shadow
root coordinates. This holds for repeated tuples too. -/
theorem sharedFoldedExpansion_relations_agree
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (LiftX : Structure (globalFunctionalPieceLanguage F) UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (eLeft : Structure.Embedding LiftX
      (foldedGlobalCanonicalLift F Left))
    (eRight : Structure.Embedding LiftX
      (foldedGlobalCanonicalLift F Right)) :
    FoldedGlobalCanonicalLiftsAgreeOn F
      (foldedFullWitness_shadowEmbedding F LiftX Left eLeft)
      (foldedFullWitness_shadowEmbedding F LiftX Right eRight) :=
  (commonFoldedFullLift_of_sharedExpansion
    F LiftX Left Right eLeft eRight).agreeOn F

end AllThoseRamseyClasses.Lifts
