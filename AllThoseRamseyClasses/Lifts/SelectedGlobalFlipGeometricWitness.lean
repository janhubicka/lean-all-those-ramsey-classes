import AllThoseRamseyClasses.Lifts.GlobalGeometricCanonicalFlip

/-!
# Retain the GENUINE selected geometric replacement witness through a full flip

The existing original-global canonical flip outputs a functional
root extension Q, an equivalent-piece certificate and a literal
full native forbidden-source diagram. Its proof extracts Q from
a genuine SelectedFunctionalChart, but the returned theorem
signature forgets Q's selected-geometric witness.

The next Track A component theorem requires precisely this
information to construct the NEW selected inner source component
and its complete generated root after the literal flip. A bare
FunctionalRootExtension with a fixed-root incompatibility profile
is not a substitute for an ACTUAL selected geometric piece.

Here we rerun the verified witness extraction and canonical
full-functional source flip, while retaining as a separate checked
conclusion the original geometric-membership certificate of Q.
This does not construct the final new geometric chart yet.
It does not weaken any source/target EHN hypotheses or alter the
meaning of the printed distinct-root canonical lift.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A global canonical relation gives an equivalent replacement Q
whose actual rooted pattern is a genuine finite forbidden
GEOMETRIC piece, and a literal forbidden full functional source
amalgam over the SAME complete Fin n root.

Unlike the older flip API, the geometric selection certificate is
not discarded by existential packaging. The complete function
interpretations and old complement map remain unchanged. -/
theorem selectedGlobalCanonicalDiagramFlip_geometricWitness
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    (T : FunctionalRootExtension P.1.root)
    (hOld : forbiddenFunctionalDiagram P.1.root F P.1.ext T)
    {UB UT : Type} (B : Structure L UB) (Target : Structure L UT)
    (jB : Structure.Embedding B Target)
    (xsB : Fin n → UB)
    (hGlobal : (globalFunctionalCanonicalLift F B).rel
      (.inr (globalPieceSymbolOf F P hn)) xsB)
    (pT : T.Carrier → UT)
    (hpT : T.str.IsEHNHomomorphismEmbedding Target pT)
    (hRoot : ∀ i : Fin n, jB (xsB i) = pT (T.rootEmbedding i)) :
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
      (FunctionalRootExtension.toEnumeratedRootedPattern
        P.1.root (Equiv.refl (Fin n)) Q)
          ∈ forbiddenGeometricFunctionalPieces F n ∧
      ∃ g : Q.Carrier → UB,
        Q.str.IsEHNHomomorphismEmbedding B g ∧
        (∀ i : Fin n, g (Q.rootEmbedding i) = xsB i) ∧
        ∃ (W : Type) (Source : Structure L W),
          F Source ∧
          ∃ (iQ : Structure.Embedding Q.str Source)
            (iT : Structure.Embedding T.str Source),
            Structure.IsFreeAmalgam Q.rootEmbedding T.rootEmbedding
              iQ iT ∧
            ∃ flip : W → UT,
              Source.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier, flip (iQ a) = jB (g a)) ∧
              (∀ b : T.Carrier, flip (iT b) = pT b) := by
  obtain ⟨_hinj, ⟨⟨rQ, eQ⟩, hQ⟩, hroots, hGlobalEq, hreal⟩ :=
    globalCanonicalRelation_compatible_witness F P hn B xsB hGlobal
  dsimp at hroots
  cases hroots
  obtain ⟨g, hg, hcoords⟩ := hreal
  have hEq : (functionalRootPieceSetoid P.1.root F).r
      P.1.ext eQ :=
    (globalFunctionalPiece_equiv_iff_fixedRoot
      P.1.root F P.1.ext eQ P.2 hQ).mp hGlobalEq
  have hGeom :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        P.1.root (Equiv.refl (Fin n)) eQ) ∈
          forbiddenGeometricFunctionalPieces F n := hQ
  have hgTarget :
      eQ.str.IsEHNHomomorphismEmbedding Target (jB ∘ g) :=
    jB.isEHNHomomorphismEmbedding.comp hg
  have hCompat :
      ∀ r : Fin n,
        (jB ∘ g) (eQ.rootEmbedding r) = pT (T.rootEmbedding r) := by
    intro r
    calc
      (jB ∘ g) (eQ.rootEmbedding r) = jB (xsB r) :=
        congrArg jB (hcoords r)
      _ = pT (T.rootEmbedding r) := hRoot r
  have hOldGlue : forbiddenFunctionalGlue P.1.root F P.1.ext T :=
    (forbiddenFunctionalDiagram_iff_glue
      P.1.root F P.1.ext T).mp hOld
  obtain ⟨W, Source, hF, iQ, iT, hfree, flip, hweak, hQmap, hTmap⟩ :=
    canonicalFunctionalFlip_actualSource P.1.root F
      P.1.ext eQ T hEq hOldGlue Target
      (jB ∘ g) pT hCompat hgTarget hpT
  exact ⟨eQ, hEq, hGeom, g, hg, hcoords,
    W, Source, hF, iQ, iT, hfree, flip,
    hweak, hQmap, hTmap⟩

end AllThoseRamseyClasses.Lifts
