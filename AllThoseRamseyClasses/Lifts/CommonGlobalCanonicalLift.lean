import AllThoseRamseyClasses.Lifts.GlobalCommonLiftAgreement

/-!
# Derive global relation agreement from a common FULL lifted structure

The witnesses A and B of the same maximal canonical lift X in the
2019 construction have a common induced expanded substructure. This
is more than merely a common old-language shadow: both complete
function interpretations AND all added piece-class relations agree.

This module packages that precise witness interface. A single
expanded structure LiftX has full embeddings into the actual GLOBAL
canonical lifts of A and B, with underlying maps equal to the given
embeddings of X in their old-language shadows.

By reflection of all new relation symbols along these FULL lifted
embeddings, every global piece-class relation is shared on the
corresponding tuples. The proof does NOT assume that arbitrary old
embeddings reflect canonical piece predicates; in general they do not.

The existence of a shared full lift is an input here, exactly the
witness condition to be supplied by the definition of
`Lifts_F` and maximality. It is NOT silently derived from merely
sharing an old-language substructure.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Concrete witness that X is induced as the SAME GLOBAL functional
lift inside the two canonical lifts of A and B.

The shadow is literally X. Both expanded embeddings must have the
prescribed old-language vertex maps; an arbitrary isomorphism of
lifted structures does not suffice without this compatibility. -/
structure CommonGlobalCanonicalLift
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (X : Structure L UX) (A : Structure L UA)
    (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) where
  lifted : Structure (globalFunctionalPieceLanguage F) UX
  shadow_eq : functionalShadowBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) lifted = X
  intoA : Structure.Embedding lifted (globalFunctionalCanonicalLift F A)
  intoB : Structure.Embedding lifted (globalFunctionalCanonicalLift F B)
  intoA_verts : ∀ x : UX, intoA x = iA x
  intoB_verts : ∀ x : UX, intoB x = iB x

/-- Full witness embeddings force equality of EVERY new canonical
piece relation on corresponding ordered root tuples. This is the
precise, reusable justification for the shared-lift step in the
published flip, not an extra combinatorial assumption. -/
theorem CommonGlobalCanonicalLift.agreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX} {A : Structure L UA}
    {B : Structure L UB}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    (h : CommonGlobalCanonicalLift F X A B iA iB) :
    GlobalCanonicalLiftsAgreeOn F iA iB := by
  intro s xs
  have hA :
      h.intoA.toFun ∘ xs = iA.toFun ∘ xs := by
    funext k
    exact h.intoA_verts (xs k)
  have hB :
      h.intoB.toFun ∘ xs = iB.toFun ∘ xs := by
    funext k
    exact h.intoB_verts (xs k)
  calc
    (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs)
        ↔ h.lifted.rel (.inr s) xs := by
          have he := h.intoA.map_rel_iff (.inr s) xs
          rw [hA] at he
          exact he
    _ ↔ (globalFunctionalCanonicalLift F B).rel (.inr s)
        (iB ∘ xs) := by
          have he := (h.intoB.map_rel_iff (.inr s) xs).symm
          rw [hB] at he
          exact he

/-- The verified geometric piece-class relation can be transferred
between the two witnesses solely from their shared full expanded
substructure and the injective weak source-root realization. -/
theorem geometricGlobalRelation_from_common_full_lift
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB : Type} {n : ℕ}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (A : Structure L UA) (B : Structure L UB)
    (X : Structure L UX)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hCommon : CommonGlobalCanonicalLift F X A B iA iB)
    (fA : V → UA)
    (hfA : Forbidden.IsEHNHomomorphismEmbedding A fA)
    (xsX : Fin n → UX)
    (hCoords : ∀ i : Fin n,
      fA (d.roots i) = iA (xsX i))
    (hinj : Function.Injective (fun i : Fin n => fA (d.roots i))) :
    (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol
        F Forbidden hFinite hForbidden d hn))
      (iB ∘ xsX) :=
  geometricGlobalRelation_shared_witness F Forbidden
    hFinite hForbidden d hn A B X
    iA iB (hCommon.agreeOn F) fA hfA xsX hCoords hinj

end AllThoseRamseyClasses.Lifts
