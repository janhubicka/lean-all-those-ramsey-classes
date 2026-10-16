import AllThoseRamseyClasses.Lifts.FoldedGlobalCanonicalRelations
import AllThoseRamseyClasses.Lifts.GlobalGeometricCanonicalFlip

/-!
# The actual forbidden-source flip from a FOLDED global relation

This is an alternative to the Section 3 canonical-lift flip.
For the auxiliary folded-root relation, one can extract an equivalent
genuine forbidden piece on any prescribed (possibly colliding) root
tuple. The already verified original functional SOURCE diagram fold
then builds a literal forbidden replacement structure together with
a weak EHN map agreeing with the old map on the entire complement.

Neither the old source nor the new source is an image quotient.
Their common full functional root still has DISTINCT SOURCE
vertices; only the root image under the target map may collide.

The theorem is conditional on membership of the folded relation in
the target witness. It is NOT a theorem about the printed canonical
lift, and does NOT claim a shared folded lift, precompactness,
maximality, or strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A true FOLDED global canonical piece-class relation in B supplies
a literal forbidden-source replacement and weak target flip without
ANY injectivity premise for the images of the ordered root tuple.

The source and replacement roots are full native functional roots;
the replacement complement and its target map remain unchanged. -/
theorem selectedFoldedGlobalCanonicalDiagramFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    (T : FunctionalRootExtension P.1.root)
    (hOld : forbiddenFunctionalDiagram P.1.root F P.1.ext T)
    {UB UT : Type} (B : Structure L UB)
    (Target : Structure L UT)
    (jB : Structure.Embedding B Target)
    (xsB : Fin n → UB)
    (hFolded : (foldedGlobalCanonicalLift F B).rel
      (.inr (globalPieceSymbolOf F P hn)) xsB)
    (pT : T.Carrier → UT)
    (hpT : T.str.IsEHNHomomorphismEmbedding Target pT)
    (hRoot : ∀ i : Fin n,
      jB (xsB i) = pT (T.rootEmbedding i)) :
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
      ∃ g : Q.Carrier → UB,
        Q.str.IsEHNHomomorphismEmbedding B g ∧
        (∀ i : Fin n, g (Q.rootEmbedding i) = xsB i) ∧
        ∃ (W : Type) (New : Structure L W),
          F New ∧
          ∃ (iQ : Structure.Embedding Q.str New)
            (iT : Structure.Embedding T.str New),
            Structure.IsFreeAmalgam Q.rootEmbedding T.rootEmbedding
              iQ iT ∧
            ∃ flip : W → UT,
              New.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier, flip (iQ a) = jB (g a)) ∧
              ∀ b : T.Carrier, flip (iT b) = pT b := by
  obtain ⟨Q, hEq, g, hg, hcoords⟩ :=
    foldedGlobalCanonicalRelation_fixedRoot_witness
      F P hn B xsB hFolded
  have hgTarget :
      Q.str.IsEHNHomomorphismEmbedding Target (jB ∘ g) :=
    jB.isEHNHomomorphismEmbedding.comp hg
  have hCompat :
      ∀ r : Fin n,
        (jB ∘ g) (Q.rootEmbedding r) =
          pT (T.rootEmbedding r) := by
    intro r
    calc
      (jB ∘ g) (Q.rootEmbedding r) = jB (xsB r) :=
        congrArg jB (hcoords r)
      _ = pT (T.rootEmbedding r) := hRoot r
  have hOldGlue : forbiddenFunctionalGlue P.1.root F P.1.ext T :=
    (forbiddenFunctionalDiagram_iff_glue
      P.1.root F P.1.ext T).mp hOld
  obtain ⟨W, New, hF, iQ, iT, hfree, flip, hweak, hQ, hT⟩ :=
    canonicalFunctionalFlip_actualSource P.1.root F
      P.1.ext Q T hEq hOldGlue Target
      (jB ∘ g) pT hCompat hgTarget hpT
  exact ⟨Q, hEq, g, hg, hcoords,
    W, New, hF, iQ, iT, hfree, flip, hweak, hQ, hT⟩

end AllThoseRamseyClasses.Lifts
