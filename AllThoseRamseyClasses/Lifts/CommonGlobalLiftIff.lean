import AllThoseRamseyClasses.Lifts.CommonGlobalCanonicalLift

/-!
# A common induced global lift iff all canonical relations agree

For a common FULL old-language substructure X of two structures A,B,
the piece-expanded relations induced on X by the GLOBAL canonical
lifts of A and B agree if and only if there exists ONE common full
expanded structure on the carrier of X, whose old functional shadow
is literally X and which fully embeds in both ambient canonical
lifts with the prescribed old vertex maps.

The forward construction is explicit: interpret every new relation
symbol on X by pulling back the corresponding canonical relation
from A; agreement ensures that the same interpretation also gives
a full embedding into B. All original function interpretations
remain exactly those of X.

The reverse direction is the already verified
`CommonGlobalCanonicalLift.agreeOn`. This equivalence is the
precise common-lift interface needed by the 2019 maximal-witness
argument; it does NOT derive agreement from merely sharing an
old-language shadow, nor assert existence of maximal witnesses.

Root-image injectivity is handled in the separate geometric
global flip theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The common induced expanded structure, with piece relations
pulled back along the left old-language embedding. -/
def commonGlobalLiftFromLeft
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    (X : Structure L UX) (A : Structure L UA)
    (iA : Structure.Embedding X A) :
    Structure (globalFunctionalPieceLanguage F) UX :=
  functionalWithExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    X
    (fun s xs =>
      (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs))

/-- The old shadow of the pulled-back lift is exactly X, including
the entire table of each old function. -/
@[simp] theorem commonGlobalLiftFromLeft_shadow
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    (X : Structure L UX) (A : Structure L UA)
    (iA : Structure.Embedding X A) :
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (commonGlobalLiftFromLeft F X A iA) = X :=
  functionalShadowBig_withExtra L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) X _

/-- The original left embedding extends to a FULL embedding of
the pulled-back lift in A's global canonical lift, without needing
additional assumptions on the right witness. -/
def commonGlobalLiftFromLeft_embedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    (X : Structure L UX) (A : Structure L UA)
    (iA : Structure.Embedding X A) :
    Structure.Embedding
      (commonGlobalLiftFromLeft F X A iA)
      (globalFunctionalCanonicalLift F A) where
  toFun := iA
  injective := iA.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl s =>
        change A.rel s.down (iA ∘ xs) ↔ X.rel s.down xs
        exact iA.map_rel_iff s.down xs
    | inr s =>
        change
          (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs) ↔
          (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs)
        exact Iff.rfl
  map_func := by
    intro s xs
    exact iA.map_func s.down xs

/-- If the right canonical lift induces the SAME added relations
on X, the old embedding X→B extends to a full expanded embedding
from the identical pullback structure constructed using A. -/
def commonGlobalLiftFromLeft_embeddingRight
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (X : Structure L UX) (A : Structure L UA)
    (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iA iB) :
    Structure.Embedding
      (commonGlobalLiftFromLeft F X A iA)
      (globalFunctionalCanonicalLift F B) where
  toFun := iB
  injective := iB.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl s =>
        change B.rel s.down (iB ∘ xs) ↔ X.rel s.down xs
        exact iB.map_rel_iff s.down xs
    | inr s =>
        change
          (globalFunctionalCanonicalLift F B).rel (.inr s) (iB ∘ xs) ↔
          (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs)
        exact (hAgree s xs).symm
  map_func := by
    intro s xs
    exact iB.map_func s.down xs

/-- Canonical relations agreeing on the common old structure are
SUFFICIENT to construct one actual common FULL expanded witness.
No maximality, completion or additional embedding is postulated. -/
def CommonGlobalCanonicalLift.ofAgreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (X : Structure L UX)
    (A : Structure L UA) (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iA iB) :
    CommonGlobalCanonicalLift F X A B iA iB where
  lifted := commonGlobalLiftFromLeft F X A iA
  shadow_eq := commonGlobalLiftFromLeft_shadow F X A iA
  intoA := commonGlobalLiftFromLeft_embedding F X A iA
  intoB := commonGlobalLiftFromLeft_embeddingRight
    F X A B iA iB hAgree
  intoA_verts := by intro _; rfl
  intoB_verts := by intro _; rfl

/-- The exact characterization needed by the maximal-lift proof:
there exists a concrete common induced GLOBAL lift with its correct
shadow and two full expanded embeddings if and only if EVERY added
canonical piece relation agrees on the common old-language carrier.

This does not assert that two arbitrary old-language embeddings
already satisfy the agreement condition. -/
theorem commonGlobalCanonicalLift_nonempty_iff_agreeOn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    (X : Structure L UX) (A : Structure L UA)
    (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) :
    Nonempty (CommonGlobalCanonicalLift F X A B iA iB) ↔
      GlobalCanonicalLiftsAgreeOn F iA iB := by
  constructor
  · rintro ⟨h⟩
    exact h.agreeOn F
  · intro h
    exact ⟨CommonGlobalCanonicalLift.ofAgreeOn
      F X A B iA iB h⟩

end AllThoseRamseyClasses.Lifts
