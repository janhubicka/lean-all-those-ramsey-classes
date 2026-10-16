import AllThoseRamseyClasses.Lifts.GlobalCanonicalWitness
import AllThoseRamseyClasses.Lifts.SelectedGlobalPieceFixedRoot

/-!
# Auxiliary folded-root canonical relations for the global forbidden-piece quotient

The original 2019 Section 3 canonical lift only records weak
realizations whose ordered root IMAGE is injective. The paper's
homomorphism-embeddings may identify vertices from a reducible root,
so that predicate cannot be applied to all geometric forbidden pieces.

Here we EXPERIMENTALLY retain the SAME genuine global piece-symbol
index and the SAME entire old functional shadow, but drop the
injectivity conjunct from the new relation's definition. It records
a genuine selected forbidden piece with a weak rooted realization,
even when several distinct SOURCE root vertices have the same
TARGET image.

The code below verifies exactly what this folded predicate means and
that a folded relation gives an equivalent replacement piece with
the SAME FULL functional root and the prescribed weak root map.

IMPORTANT: This is NOT the printed 2019 lift. In particular the
absence of distinct-root filtering may harm precompactness when
the forbidden family has unbounded root widths. We do NOT claim
precompactness, amalgamation or a correction of the full theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The literal global piece-class relation without the distinct-root
filter; every realizing piece is still an ACTUAL geometric forbidden
piece from the indexed global equivalence class. -/
def foldedGlobalCanonicalExtra
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → W) : Prop :=
  ∃ Q : SelectedFunctionalChart F s.1.1,
    Quotient.mk (globalFunctionalPieceSetoid F s.1.1) Q = s.2 ∧
      FunctionalRootRealization Q.1.pattern A xs

/-- An AUXILIARY lift, preserving the original functions and old
relations and using the ordinary global piece-class symbols, but
also allowing repeated coordinates in their root realizations. -/
def foldedGlobalCanonicalLift
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W) :
    Structure (globalFunctionalPieceLanguage F) W :=
  functionalWithExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    A (foldedGlobalCanonicalExtra F A)

@[simp] theorem foldedGlobalCanonicalLift_shadow
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W) :
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (foldedGlobalCanonicalLift F A) = A :=
  functionalShadowBig_withExtra L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) A _

/-- An occurrence of an auxiliary folded global relation is exactly
a genuine selected forbidden piece of the given global class with a
weak realization on the chosen, POSSIBLY NONINJECTIVE, root tuple. -/
theorem foldedGlobalCanonicalRelation_of_symbol_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (xs : Fin n → W) :
    (foldedGlobalCanonicalLift F A).rel
      (.inr (globalPieceSymbolOf F P hn)) xs ↔
      ∃ Q : SelectedFunctionalChart F n,
        (globalFunctionalPieceSetoid F n).r P Q ∧
        FunctionalRootRealization Q.1.pattern A xs := by
  change
    (∃ Q : SelectedFunctionalChart F n,
      Quotient.mk (globalFunctionalPieceSetoid F n) Q =
        Quotient.mk (globalFunctionalPieceSetoid F n) P ∧
      FunctionalRootRealization Q.1.pattern A xs) ↔ _
  constructor
  · rintro ⟨Q, hEq, hReal⟩
    have hQP : (globalFunctionalPieceSetoid F n).r Q P :=
      Quotient.exact hEq
    exact ⟨Q, (globalFunctionalPieceSetoid F n).iseqv.symm hQP,
      hReal⟩
  · rintro ⟨Q, hEq, hReal⟩
    exact ⟨Q, Quotient.sound
      ((globalFunctionalPieceSetoid F n).iseqv.symm hEq), hReal⟩

/-- Every weak realization of a selected piece, EVEN WITH COLLIDING
ROOT IMAGES, gives the new auxiliary folded canonical class relation.
This theorem deliberately has no root-image injectivity hypothesis. -/
theorem foldedGlobalCanonicalRelation_of_selected_weak
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (f : P.1.ext.Carrier → W)
    (hf : P.1.ext.str.IsEHNHomomorphismEmbedding A f) :
    (foldedGlobalCanonicalLift F A).rel
      (.inr (globalPieceSymbolOf F P hn))
      (fun i : Fin n => f (P.1.ext.rootEmbedding i)) := by
  apply (foldedGlobalCanonicalRelation_of_symbol_iff
    F P hn A (fun i => f (P.1.ext.rootEmbedding i))).mpr
  exact ⟨P, (globalFunctionalPieceSetoid F n).iseqv.refl P,
    f, hf, fun _ => rfl⟩

/-- A genuine folded class relation supplies a selected forbidden
replacement Q having the SAME COMPLETE native root structure as P.
The returned weak realization has exactly the displayed coordinates,
without any requirement that the coordinates be distinct. -/
theorem foldedGlobalCanonicalRelation_fixedRoot_witness
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (xs : Fin n → W)
    (h : (foldedGlobalCanonicalLift F A).rel
      (.inr (globalPieceSymbolOf F P hn)) xs) :
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
      ∃ g : Q.Carrier → W,
        Q.str.IsEHNHomomorphismEmbedding A g ∧
        ∀ i : Fin n, g (Q.rootEmbedding i) = xs i := by
  obtain ⟨Q, hEq, hReal⟩ :=
    (foldedGlobalCanonicalRelation_of_symbol_iff
      F P hn A xs).mp h
  have hRoot : P.1.root = Q.1.root :=
    globalFunctionalPiece_equiv_root_eq F P Q hEq
  rcases Q with ⟨⟨rQ, eQ⟩, hQ⟩
  dsimp at hRoot
  cases hRoot
  have hFixed :
      (functionalRootPieceSetoid P.1.root F).r P.1.ext eQ :=
    (globalFunctionalPiece_equiv_iff_fixedRoot
      P.1.root F P.1.ext eQ P.2 hQ).mp hEq
  obtain ⟨g, hg, hcoords⟩ := hReal
  exact ⟨eQ, hFixed, g, hg, hcoords⟩

/-- Every original (injective-coordinate) canonical relation also
appears in the auxiliary folded lift, but the converse is not
asserted. -/
theorem globalCanonicalRelation_implies_folded
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → W)
    (h : (globalFunctionalCanonicalLift F A).rel (.inr s) xs) :
    (foldedGlobalCanonicalLift F A).rel (.inr s) xs := by
  obtain ⟨_hInjective, Q, hClass, hReal⟩ :=
    (globalFunctionalCanonicalRelation_iff F A s xs).mp h
  exact ⟨Q, hClass, hReal⟩

end AllThoseRamseyClasses.Lifts
