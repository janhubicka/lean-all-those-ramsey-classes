import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# A common induced GLOBAL functional lift relation on two witnesses

Two witnesses of the same lifted substructure must agree about every
new piece-class relation on their common vertex substructure. We
express that condition for the actual GLOBAL class-indexed language
and prove the elementary but essential relation transfer lemma.

The geometric version shows: if a genuine finite forbidden source
maps weakly into the left witness with an INJECTIVE ordered root image
in the common substructure, then its genuine global piece-class
relation also holds on the matching tuple of the right witness.

This is the logical core of the shared-canonical-lift step in the
2019 flip proof, stated independently of the later source replacement.
No claim is made that arbitrary maximal witnesses necessarily agree
without first proving the induced-lift witness property.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The two global canonical functional lifts induce the SAME added
piece-class relations on a designated common full substructure.

The agreement concerns EVERY positive-width global symbol and EVERY
ordered tuple from the common carrier. The original functions are
preserved by the common full embeddings, independently of this
extra-relation agreement. -/
def GlobalCanonicalLiftsAgreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX} {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) : Prop :=
  ∀ (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UX),
    (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs) ↔
      (globalFunctionalCanonicalLift F B).rel (.inr s) (iB ∘ xs)

/-- All globally indexed canonical relations are transported across
two ambient witnesses whenever their induced lifted structures
agree on the common full substructure. -/
theorem globalCanonicalRelation_transfer_common
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX} {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iA iB)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UX)
    (hA : (globalFunctionalCanonicalLift F A).rel (.inr s)
      (iA ∘ xs)) :
    (globalFunctionalCanonicalLift F B).rel (.inr s)
      (iB ∘ xs) :=
  (hAgree s xs).mp hA

/-- The geometric forbidden piece's actual GLOBAL class relation
transfers from a weak realization in the left witness to the right
witness over their common lifted substructure.

The source root image is explicitly assumed injective. This is
necessary because the paper's canonical relation requires distinct
coordinates, while a weak EHN map need not be globally injective. -/
theorem geometricGlobalRelation_shared_witness
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB : Type} {n : ℕ}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (A : Structure L UA) (B : Structure L UB)
    (X : Structure L UX)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iA iB)
    (fA : V → UA)
    (hfA : Forbidden.IsEHNHomomorphismEmbedding A fA)
    (xsX : Fin n → UX)
    (hCoords : ∀ i : Fin n,
      fA (d.roots i) = iA (xsX i))
    (hinj : Function.Injective (fun i : Fin n => fA (d.roots i))) :
    (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol
        F Forbidden hFinite hForbidden d hn))
      (iB ∘ xsX) := by
  let s := geometricGlobalPieceSymbol F Forbidden hFinite hForbidden d hn
  have hRelA :
      (globalFunctionalCanonicalLift F A).rel (.inr s)
        (fun i : Fin n => fA (d.roots i)) :=
    geometricGlobalCanonicalRelation_of_weak F Forbidden
      hFinite hForbidden d hn A fA hfA hinj
  have hTuple :
      (fun i : Fin n => fA (d.roots i)) = (iA ∘ xsX) := by
    funext i
    exact hCoords i
  rw [hTuple] at hRelA
  exact (hAgree s xsX).mp hRelA

end AllThoseRamseyClasses.Lifts
