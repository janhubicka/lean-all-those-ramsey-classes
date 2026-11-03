import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguageBig
import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track E: EHN projections survive forgetting arbitrary added RELATION tags

The actual functional partite construction gives EHN projections
in the EXPANDED finite-family lift language. Before applying the
native forbidden-family weak-locality lemmas, one must show that
forgetting the added relations yields an EHN projection of the
unchanged native functional shadows. Global weak preservation
is immediate, but irreducible-test preservation is NOT automatic:
a full old-language irreducible E need not carry the same extra
tag predicates as its ambient image.

The correct route is to pull the ambient extra relations back to
E along its FULL old native embedding. This makes an actual FULL
embedding E+ into the expanded source. Since E is old-irreducible,
E+ is irreducible too: every full free amalgamation of expanded
structures induces a full free amalgamation of their native
shadows, preserving ALL old set-valued function fibres.

Apply the EXPANDED EHN map to this actual irreducible E+, then
forget the extra predicates in the resulting full embedding.
The result protects the original old-language E, as required.

These statements work for arbitrary new relation symbols and
arities, arbitrary native function arities including nullary,
and noninjective EHN projections. They are not restricted to
the folded finite named family and do not assume any Ramsey
or forbidden-family conclusion.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u w
variable {L : Language.{u}}

/-- A genuine full functional free amalgam of expansions by
arbitrary additional RELATIONS remains a genuine full native
functional free amalgam after forgetting the extra relations.

In particular, the complete old set-valued function fibres,
not just their positive incidences, satisfy the free-amalgam
factorization law. -/
theorem functionalShadowBig_freeAmalgam
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {UH UA UB UC : Type}
    {Root : Structure (functionalLiftLanguageBig L New ar) UH}
    {A : Structure (functionalLiftLanguageBig L New ar) UA}
    {B : Structure (functionalLiftLanguageBig L New ar) UB}
    {C : Structure (functionalLiftLanguageBig L New ar) UC}
    {sA : Structure.Embedding Root A}
    {sB : Structure.Embedding Root B}
    {iA : Structure.Embedding A C}
    {iB : Structure.Embedding B C}
    (hFree : Structure.IsFreeAmalgam sA sB iA iB) :
    Structure.IsFreeAmalgam
      (functionalShadowBigEmbedding L New ar sA)
      (functionalShadowBigEmbedding L New ar sB)
      (functionalShadowBigEmbedding L New ar iA)
      (functionalShadowBigEmbedding L New ar iB) where
  covers := hFree.covers
  overlap := hFree.overlap
  rel_iff := fun R xs => hFree.rel_iff (.inl (ULift.up R)) xs
  func_iff := fun F xs y => hFree.func_iff (ULift.up F) xs y

/-- Irreducibility of the exact NATIVE functional shadow implies
irreducibility of any expansion by additional relations. This
direction is essential for protecting old native irreducible
tests under an expanded EHN homomorphism-embedding. -/
theorem functionalLift_irreducible_of_shadow
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {UA : Type}
    (A : Structure (functionalLiftLanguageBig L New ar) UA)
    (hShadow :
      (functionalShadowBig L New ar A).Irreducible) :
    A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  exact hShadow
    (functionalShadowBig_freeAmalgam L New ar hFree)
    (functionalShadowBigEmbedding L New ar e)

/-- An EHN homomorphism-embedding between arbitrary finite-family
RELATIONAL expansions descends to an EHN
homomorphism-embedding of their unchanged old full functional
shadows. The weak map need NOT be globally injective or full.

The critical point is that every old irreducible full test is
temporarily expanded by the exact predicates induced from its
ambient full embedding before applying the EHN test property. -/
theorem functionalEHN_shadowBig
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {UA UB : Type}
    {X : Structure (functionalLiftLanguageBig L New ar) UA}
    {Y : Structure (functionalLiftLanguageBig L New ar) UB}
    {p : UA → UB}
    (hp : X.IsEHNHomomorphismEmbedding Y p) :
    (functionalShadowBig L New ar X).IsEHNHomomorphismEmbedding
      (functionalShadowBig L New ar Y) p := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R xs hR
    exact hp.1.1 (.inl (ULift.up R)) xs hR
  · intro F xs y hy
    exact hp.1.2 (ULift.up F) xs y hy
  · intro ZE E hE e
    let EPlus : Structure (functionalLiftLanguageBig L New ar) ZE :=
      functionalWithExtraBig L New ar E
        (fun tag xs => X.rel (.inr tag) (e ∘ xs))
    have hOld : functionalShadowBig L New ar EPlus = E :=
      functionalShadowBig_withExtra L New ar E _
    let ePlus : Structure.Embedding EPlus X := {
      toFun := e
      injective := e.injective
      map_rel_iff := by
        intro R xs
        cases R with
        | inl R => exact e.map_rel_iff R.down xs
        | inr tag => exact Iff.rfl
      map_func := by
        intro F xs
        exact e.map_func F.down xs
    }
    have hIPlus : EPlus.Irreducible :=
      functionalLift_irreducible_of_shadow
        L New ar EPlus (by rw [hOld]; exact hE)
    obtain ⟨eY, heY⟩ := hp.2 EPlus hIPlus ePlus
    let eOld : Structure.Embedding E
        (functionalShadowBig L New ar Y) := {
      toFun := eY
      injective := eY.injective
      map_rel_iff := by
        intro R xs
        exact eY.map_rel_iff (.inl (ULift.up R)) xs
      map_func := by
        intro F xs
        exact eY.map_func (ULift.up F) xs
    }
    exact ⟨eOld, by
      intro x
      exact heY x⟩

end AllThoseRamseyClasses.Lifts
