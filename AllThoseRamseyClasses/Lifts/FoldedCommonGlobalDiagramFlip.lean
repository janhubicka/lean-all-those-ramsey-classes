import AllThoseRamseyClasses.Lifts.FoldedGlobalDiagramFlip

/-!
# Conditional shared FOLDED canonical lift and collision-tolerant diagram flip

A common FULL folded canonical lift is a genuine shared expansion of
the old common functional root X in two ambient witnesses. It forces
agreement of the auxiliary folded piece-class relations, including
relations on root tuples whose target coordinates are repeated.

This gives a LITERAL forbidden-source replacement from a weak piece
map in Left and an agreeing complete-root map on the old complement,
without assuming injectivity of the selected ROOT IMAGE.

IMPORTANT: existence of such a common folded lift for two witnesses
of a maximal folded expansion is NOT asserted here. This is a
conditional construction for an AUXILIARY alternative lift, not
the printed 2019 distinct-root construction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- Agreement of genuine auxiliary folded piece-class predicates on
the same complete old functional substructure X of two witnesses. -/
def FoldedGlobalCanonicalLiftsAgreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB}
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right) : Prop :=
  ∀ (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UX),
    (foldedGlobalCanonicalLift F Left).rel (.inr s)
      (iLeft ∘ xs) ↔
    (foldedGlobalCanonicalLift F Right).rel (.inr s)
      (iRight ∘ xs)

/-- Concrete full embeddings of one actual folded lifted root into
both folded canonical witness lifts, with underlying old-language
embeddings fixed in advance. -/
structure CommonFoldedGlobalCanonicalLift
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (X : Structure L UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right) where
  lifted : Structure (globalFunctionalPieceLanguage F) UX
  shadow_eq : functionalShadowBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) lifted = X
  intoLeft : Structure.Embedding lifted (foldedGlobalCanonicalLift F Left)
  intoRight : Structure.Embedding lifted (foldedGlobalCanonicalLift F Right)
  intoLeft_verts : ∀ x : UX, intoLeft x = iLeft x
  intoRight_verts : ∀ x : UX, intoRight x = iRight x

/-- A common FULL folded lift forces the same folded relation on
each tuple of the common root. The proof uses full reflection of
relation symbols in both lifted embeddings; it does not assume
that ordinary shadow embeddings reflect folded predicates. -/
theorem CommonFoldedGlobalCanonicalLift.agreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    (h : CommonFoldedGlobalCanonicalLift F X Left Right
      iLeft iRight) :
    FoldedGlobalCanonicalLiftsAgreeOn F iLeft iRight := by
  intro s xs
  have hL :
      h.intoLeft.toFun ∘ xs = iLeft.toFun ∘ xs := by
    funext k
    exact h.intoLeft_verts (xs k)
  have hR :
      h.intoRight.toFun ∘ xs = iRight.toFun ∘ xs := by
    funext k
    exact h.intoRight_verts (xs k)
  calc
    (foldedGlobalCanonicalLift F Left).rel (.inr s) (iLeft ∘ xs)
        ↔ (foldedGlobalCanonicalLift F Left).rel (.inr s)
            (h.intoLeft ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun t : Fin (globalFunctionalPieceArity F s) → UA =>
              (foldedGlobalCanonicalLift F Left).rel (.inr s) t)
            hL.symm)
    _ ↔ h.lifted.rel (.inr s) xs :=
      h.intoLeft.map_rel_iff (.inr s) xs
    _ ↔ (foldedGlobalCanonicalLift F Right).rel (.inr s)
        (h.intoRight ∘ xs) :=
      (h.intoRight.map_rel_iff (.inr s) xs).symm
    _ ↔ (foldedGlobalCanonicalLift F Right).rel (.inr s)
        (iRight ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun t : Fin (globalFunctionalPieceArity F s) → UB =>
              (foldedGlobalCanonicalLift F Right).rel (.inr s) t)
            hR)

/-- From an actual common FULL auxiliary folded lift, weak maps
of a genuine forbidden piece into Left and of its unchanged full
complement into Target construct a forbidden replacement source
whose piece maps into Right. Crucially NO root-image injectivity
is assumed.

Compatible ordered coordinates in the common root still ensure
agreement of the new and unchanged piece maps on the whole
functional root, even when target coordinates collide. -/
theorem selectedFoldedCommonFullLiftDiagramFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n) (hn : 0 < n)
    (T : FunctionalRootExtension P.1.root)
    (hOld : forbiddenFunctionalDiagram P.1.root F P.1.ext T)
    {UX UA UB UT : Type}
    (X : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hCommon : CommonFoldedGlobalCanonicalLift
      F X Left Right iLeft iRight)
    (hTargetAgree : ∀ x : UX,
      jLeft (iLeft x) = jRight (iRight x))
    (pLeft : P.1.ext.Carrier → UA)
    (hpLeft : P.1.ext.str.IsEHNHomomorphismEmbedding Left pLeft)
    (pT : T.Carrier → UT)
    (hpT : T.str.IsEHNHomomorphismEmbedding Target pT)
    (xsX : Fin n → UX)
    (hRootLeft : ∀ i : Fin n,
      pLeft (P.1.ext.rootEmbedding i) = iLeft (xsX i))
    (hRootTarget : ∀ i : Fin n,
      jLeft (pLeft (P.1.ext.rootEmbedding i)) =
        pT (T.rootEmbedding i)) :
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
      ∃ g : Q.Carrier → UB,
        Q.str.IsEHNHomomorphismEmbedding Right g ∧
        (∀ i : Fin n, g (Q.rootEmbedding i) = iRight (xsX i)) ∧
        ∃ (W : Type) (New : Structure L W),
          F New ∧
          ∃ (iQ : Structure.Embedding Q.str New)
            (iT : Structure.Embedding T.str New),
            Structure.IsFreeAmalgam Q.rootEmbedding T.rootEmbedding
              iQ iT ∧
            ∃ flip : W → UT,
              New.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier, flip (iQ a) = jRight (g a)) ∧
              ∀ b : T.Carrier, flip (iT b) = pT b := by
  have hRelLeft :
      (foldedGlobalCanonicalLift F Left).rel
        (.inr (globalPieceSymbolOf F P hn))
        (fun i : Fin n => pLeft (P.1.ext.rootEmbedding i)) :=
    foldedGlobalCanonicalRelation_of_selected_weak
      F P hn Left pLeft hpLeft
  have hTuple :
      (fun i : Fin n => pLeft (P.1.ext.rootEmbedding i)) =
        (iLeft ∘ xsX) := by
    funext i
    exact hRootLeft i
  rw [hTuple] at hRelLeft
  have hRelRight :
      (foldedGlobalCanonicalLift F Right).rel
        (.inr (globalPieceSymbolOf F P hn))
        (iRight ∘ xsX) :=
    (hCommon.agreeOn F (globalPieceSymbolOf F P hn) xsX).mp
      hRelLeft
  have hRightRoot (i : Fin n) :
      jRight (iRight (xsX i)) = pT (T.rootEmbedding i) := by
    calc
      jRight (iRight (xsX i)) =
          jLeft (iLeft (xsX i)) :=
        (hTargetAgree (xsX i)).symm
      _ = jLeft (pLeft (P.1.ext.rootEmbedding i)) :=
        congrArg jLeft (hRootLeft i).symm
      _ = pT (T.rootEmbedding i) := hRootTarget i
  exact selectedFoldedGlobalCanonicalDiagramFlip
    F P hn T hOld Right Target jRight
      (iRight ∘ xsX) hRelRight pT hpT hRightRoot

end AllThoseRamseyClasses.Lifts
