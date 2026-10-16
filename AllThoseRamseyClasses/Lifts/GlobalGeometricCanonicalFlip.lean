import AllThoseRamseyClasses.Lifts.GlobalCanonicalFixedRootWitness
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge

/-!
# A GLOBAL canonical relation produces a genuine forbidden-source flip

This combines the already verified global quotient-indexed canonical
piece lift with the actual geometric forbidden-source decomposition.

A global piece-class relation in a second witness B supplies an ACTUAL
selected replacement piece Q, not an arbitrary nonpiece extension.
The nonempty forbidden-complement theorem identifies its complete
functional root with that of the original piece. A full embedding of
B into a common target transports the replacement's weak EHN map.

The original forbidden source A is already a full functional free
amalgam of its selected geometric piece and its closed complement
over the entire standard ordered Fin n root. We therefore invoke the
verified actual-source flip and preserve the old map on EVERY vertex
of the complement.

The explicit extra relation demands injective roots. In particular,
when its coordinates map to the roots of a weak source map f through
a FULL embedding of B, the root image of f is injective. This is not
a consequence of the weak source map by itself.

This module proves the geometric flip from a GLOBAL relation in B.
To obtain the paper's unrestricted flip from TWO maximal lift
witnesses, one still needs the common-lift identification of that
global relation and the tuple-surjective-image reduction where
noninjective forbidden source maps arise.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A genuine GLOBAL canonical relation in B supplies a selected
replacement in the same complete root, and the verified actual-source
diagram flip constructs a forbidden source and a weak EHN map.

The complement T may be arbitrary. A later application specializes it
to the original geometric source's closed complementary component. -/
theorem selectedGlobalCanonicalDiagramFlip
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
  obtain ⟨_hinj, Q, hEq, g, hg, hcoords⟩ :=
    globalCanonicalRelation_fixedRoot_witness F P hn B xsB hGlobal
  have hgTarget :
      Q.str.IsEHNHomomorphismEmbedding Target (jB ∘ g) :=
    jB.isEHNHomomorphismEmbedding.comp hg
  have hCompat :
      ∀ r : Fin n,
        (jB ∘ g) (Q.rootEmbedding r) = pT (T.rootEmbedding r) := by
    intro r
    calc
      (jB ∘ g) (Q.rootEmbedding r) = jB (xsB r) :=
        congrArg jB (hcoords r)
      _ = pT (T.rootEmbedding r) := hRoot r
  have hOldGlue : forbiddenFunctionalGlue P.1.root F P.1.ext T :=
    (forbiddenFunctionalDiagram_iff_glue
      P.1.root F P.1.ext T).mp hOld
  obtain ⟨W, Source, hF, iQ, iT, hfree, flip, hweak, hQ, hT⟩ :=
    canonicalFunctionalFlip_actualSource P.1.root F
      P.1.ext Q T hEq hOldGlue Target
      (jB ∘ g) pT hCompat hgTarget hpT
  exact ⟨Q, hEq, g, hg, hcoords, W, Source, hF,
    iQ, iT, hfree, flip, hweak, hQ, hT⟩

/-- An embedded GLOBAL canonical root tuple cannot coincide with
the image of a noninjective tuple in the original weak forbidden map.
No injectivity assumption on the weak map f is silently introduced. -/
theorem geometricGlobalCanonicalRootImage_injective
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UB UT : Type} (A : Structure L V)
    (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) (hn : 0 < n)
    (B : Structure L UB) (Target : Structure L UT)
    (jB : Structure.Embedding B Target)
    (f : V → UT) (xsB : Fin n → UB)
    (hCoordinates : ∀ i : Fin n, jB (xsB i) = f (d.roots i))
    (hGlobal : (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol F A hFinite hFA d hn)) xsB) :
    Function.Injective (fun i : Fin n => f (d.roots i)) := by
  have hinj : Function.Injective xsB :=
    (globalFunctionalCanonicalRelation_iff F B
      (geometricGlobalPieceSymbol F A hFinite hFA d hn) xsB).mp
      hGlobal |>.1
  intro i j hij
  apply hinj
  apply jB.injective
  calc
    jB (xsB i) = f (d.roots i) := hCoordinates i
    _ = f (d.roots j) := hij
    _ = jB (xsB j) := (hCoordinates j).symm

/-- The GLOBAL lift's piece relation in another witness gives an
ACTUAL forbidden-source replacement of a geometric minimal-cut piece.

The replacement weak map agrees with the old weak map on the entire
unchanged closed complement, while its new piece map factors through
the full embedding of the second witness B into the common target.

Only the existence of the canonical relation in B is required here;
the left-witness shared-relation implication is a separate theorem. -/
theorem geometricGlobalCanonicalFlip_of_relation
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UB UT : Type} (A : Structure L V)
    (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) (hn : 0 < n)
    (Target : Structure L UT)
    (f : V → UT) (hf : A.IsEHNHomomorphismEmbedding Target f)
    (B : Structure L UB) (jB : Structure.Embedding B Target)
    (xsB : Fin n → UB)
    (hCoordinates : ∀ i : Fin n, jB (xsB i) = f (d.roots i))
    (hGlobal : (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol F A hFinite hFA d hn)) xsB) :
    let P := geometricGlobalSelectedChart F A hFinite hFA d
    let T := geometricGlobalComplementChart A d
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
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
              (∀ b : T.Carrier, flip (iT b) = f b.1) := by
  let P : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F A hFinite hFA d
  let T : FunctionalRootExtension P.1.root :=
    geometricGlobalComplementChart A d
  let pT : T.Carrier → UT := fun b => f b.1
  have hpT : T.str.IsEHNHomomorphismEmbedding Target pT :=
    hf.comp
      (functionalComponentComplementEmbedding A (Set.range d.roots)
        d.minimal.1 d.left).isEHNHomomorphismEmbedding
  have hOld : forbiddenFunctionalDiagram P.1.root F P.1.ext T :=
    geometricGlobalSource_has_forbidden_diagram
      F A hFinite hFA d
  have hGlobalP : (globalFunctionalCanonicalLift F B).rel
      (.inr (globalPieceSymbolOf F P hn)) xsB := by
    change (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol F A hFinite hFA d hn)) xsB
    exact hGlobal
  have hRoot :
      ∀ i : Fin n, jB (xsB i) = pT (T.rootEmbedding i) := by
    intro i
    change jB (xsB i) = f (d.roots i)
    exact hCoordinates i
  exact selectedGlobalCanonicalDiagramFlip
    F P hn T hOld B Target jB xsB hGlobalP
    pT hpT hRoot

end AllThoseRamseyClasses.Lifts
