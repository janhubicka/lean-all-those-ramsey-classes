import AllThoseRamseyClasses.Lifts.GlobalCanonicalWitness
import AllThoseRamseyClasses.Lifts.SelectedGlobalPieceFixedRoot

/-!
# Extract global canonical replacement pieces in one FULL functional root

The 2019 global canonical piece relation returns an ACTUAL selected
forbidden piece from the same global incompatibility class.

The nonempty forbidden-complement theorem guarantees its entire
native functional root equals that of the original selected piece.
This is stronger than merely having the same root width, and now
lets us rewrite the dependent full root extension into exactly the
chart used by the verified fixed-root canonical flip.

Unlike the earlier temporary single-class construction, the global
relation here only admits genuine forbidden geometric pieces as
witnesses. No arbitrary nonpiece extension is inserted into its
canonical relation interpretation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A true global canonical relation yields an ACTUAL selected
replacement piece in the same full functional root chart as the
original, together with its weak realization on the prescribed
injective ordered tuple. -/
theorem globalCanonicalRelation_fixedRoot_witness
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (xs : Fin n → W)
    (h : (globalFunctionalCanonicalLift F A).rel
      (.inr (globalPieceSymbolOf F P hn)) xs) :
    Function.Injective xs ∧
      ∃ Q : FunctionalRootExtension P.1.root,
        (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
        ∃ g : Q.Carrier → W,
          Q.str.IsEHNHomomorphismEmbedding A g ∧
          ∀ i : Fin n, g (Q.rootEmbedding i) = xs i := by
  obtain ⟨hinj, ⟨⟨rQ, eQ⟩, hQ⟩, hroot, hglobal, hreal⟩ :=
    globalCanonicalRelation_compatible_witness F P hn A xs h
  obtain ⟨g, hg, hcoords⟩ := hreal
  dsimp at hroot
  cases hroot
  have hfixed :
      (functionalRootPieceSetoid P.1.root F).r P.1.ext eQ :=
    (globalFunctionalPiece_equiv_iff_fixedRoot
      P.1.root F P.1.ext eQ P.2 hQ).mp hglobal
  exact ⟨hinj, eQ, hfixed, g, hg, hcoords⟩

/-- In particular, equality of one genuine global piece-class
relation between two ambient witnesses supplies a fixed-root
replacement map in the second witness. The input weak realization
in the first witness must have an injective root image, as the
canonical lift requires. -/
theorem globalCanonicalShared_fixedRoot_witness
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n) (hn : 0 < n)
    {W Z : Type}
    (A : Structure L W) (B : Structure L Z)
    (f : P.1.ext.Carrier → W)
    (hf : P.1.ext.str.IsEHNHomomorphismEmbedding A f)
    (hinj : Function.Injective
      (fun i : Fin n => f (P.1.ext.rootEmbedding i)))
    (xsB : Fin n → Z)
    (hShared :
      (globalFunctionalCanonicalLift F A).rel
        (.inr (globalPieceSymbolOf F P hn))
        (fun i : Fin n => f (P.1.ext.rootEmbedding i)) →
      (globalFunctionalCanonicalLift F B).rel
        (.inr (globalPieceSymbolOf F P hn)) xsB) :
    Function.Injective xsB ∧
      ∃ Q : FunctionalRootExtension P.1.root,
        (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
        ∃ g : Q.Carrier → Z,
          Q.str.IsEHNHomomorphismEmbedding B g ∧
          ∀ i : Fin n, g (Q.rootEmbedding i) = xsB i := by
  have hA : (globalFunctionalCanonicalLift F A).rel
      (.inr (globalPieceSymbolOf F P hn))
      (fun i : Fin n => f (P.1.ext.rootEmbedding i)) :=
    globalCanonicalRelation_of_selected_weak F P hn A f hf hinj
  exact globalCanonicalRelation_fixedRoot_witness F P hn B xsB
    (hShared hA)

end AllThoseRamseyClasses.Lifts
