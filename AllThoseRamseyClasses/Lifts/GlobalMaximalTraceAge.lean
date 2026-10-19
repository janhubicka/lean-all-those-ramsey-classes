import AllThoseRamseyClasses.Lifts.GlobalCanonicalInducedTrace
import AllThoseRamseyClasses.Lifts.RegularGlobalMaximalWitnessExistence

/-!
# Hereditary finite maximal-trace age of the original regular global lift

This is the class-theoretic assembly of two separately verified steps
in the ORIGINAL 2019 Section 3 construction, with the old functional
language retained exactly:

* For a regular family, finite observations on any fixed finite root
  yield a finite allowed witness maximal along that root (choosing
  the allowed class to contain only finite native structures).
* The FULL induced global-piece trace of such a witness on its root
  preserves all original old relations and complete function fibres.
  Maximality passes to every smaller full root.

Consequently these genuine finite witness traces form a hereditary
age, and every finite allowed native structure has an expanded trace
in the age. If the native class is hereditary under full embeddings,
the reduct of the expanded age is EXACTLY that native class.

This does not prove strong amalgamation or Ramsey for the regular
infinite-family lift. In particular the printed Claim 2 /
noninjective weak root-image issue remains open and is NOT hidden
in the definition of age membership.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Restrict an arbitrary allowed native functional class to
FINITE witnesses. The original maximality theorem quantifies
over precisely this finite class in the intended Section 3 age. -/
def FiniteGlobalAllowed
    (K : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (C : Structure L W) : Prop :=
  K C ∧ Finite W

/-- The TRUE hereditary finite maximal trace age of the original
root-injective global canonical piece-class lift.

The old shadow of Y embeds FULLY in an allowed FINITE witness W
which is maximal along the displayed image among finite allowed
extensions, and EVERY additional relation table of Y is the
FULL induced canonical trace seen inside W. The witness need NOT
be globally maximal on its own carrier.

The family F may be infinite and the lifted signature need not
be finite, though later precompactness uses regularity. -/
def IsGlobalFiniteMaximalTrace
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) V) : Prop :=
  Finite V ∧
  ∃ (UW : Type) (W : Structure L UW),
    Finite UW ∧ K W ∧
    ∃ (iW : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y) W),
      GlobalCanonicalMaximalAlong F (FiniteGlobalAllowed K) iW ∧
      ∀ (s : GlobalFunctionalPieceSymbol F)
        (xs : Fin (globalFunctionalPieceArity F s) → V),
        Y.rel (.inr s) xs ↔
          (globalFunctionalCanonicalLift F W).rel
            (.inr s) (iW ∘ xs)

/-- An actual full induced trace of a finite allowed maximizing
witness belongs to the finite global maximal-trace age. -/
theorem globalCanonicalInducedTrace_mem_maximalAge
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UW : Type} [Finite UX] [Finite UW]
    {X : Structure L UX} {W : Structure L UW}
    (iW : Structure.Embedding X W)
    (hAllowed : K W)
    (hMax : GlobalCanonicalMaximalAlong F
      (FiniteGlobalAllowed K) iW) :
    IsGlobalFiniteMaximalTrace F K
      (globalCanonicalInducedTrace F iW) := by
  refine ⟨inferInstance, UW, W, inferInstance, hAllowed, ?_⟩
  refine ⟨iW, hMax, ?_⟩
  intro s xs
  exact Iff.rfl

/-- Full expanded embeddings preserve membership in the
finite global maximal-trace age. This is genuinely hereditary
under arbitrary FULL expanded substructures, not an incorrect
claim that canonical lifts themselves commute with restriction. -/
theorem IsGlobalFiniteMaximalTrace.of_embedding
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {VA VB : Type}
    {A : Structure (globalFunctionalPieceLanguage F) VA}
    {B : Structure (globalFunctionalPieceLanguage F) VB}
    (hB : IsGlobalFiniteMaximalTrace F K B)
    (e : Structure.Embedding A B) :
    IsGlobalFiniteMaximalTrace F K A := by
  rcases hB with
    ⟨hFinB, UW, W, hFinW, hAllowedW, iW, hMax, hBrel⟩
  letI : Finite VB := hFinB
  have hFinA : Finite VA :=
    Finite.of_injective e e.injective
  let shE : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) A)
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) B) :=
    functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) e
  have hMaxSmall :
      GlobalCanonicalMaximalAlong F
        (FiniteGlobalAllowed K) (iW.comp shE) :=
    GlobalCanonicalMaximalAlong.restrict_root
      F (FiniteGlobalAllowed K) iW shE hMax
  refine ⟨hFinA, UW, W, hFinW, hAllowedW,
    iW.comp shE, hMaxSmall, ?_⟩
  intro s xs
  have he := e.map_rel_iff (.inr s) xs
  have hw := hBrel s (shE ∘ xs)
  change B.rel (.inr s) (shE ∘ xs) ↔
      A.rel (.inr s) xs at he
  change A.rel (.inr s) xs ↔
    (globalFunctionalCanonicalLift F W).rel (.inr s)
      ((iW.comp shE) ∘ xs)
  exact he.symm.trans hw

/-- Every finite native allowed structure A has an ACTUAL
expanded global maximal induced trace on the SAME carrier.
Regularity supplies the maximum finite root profile and the
finite allowed witness; no strong AP/JEP is invoked. -/
theorem globalFiniteMaximalTraceAge_exists_above
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {V : Type} [Finite V]
    (A : Structure L V) (hA : K A) :
    ∃ (Y : Structure (globalFunctionalPieceLanguage F) V),
      functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y = A ∧
      IsGlobalFiniteMaximalTrace F K Y := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let idA : Structure.Embedding A A := Structure.Embedding.id A
  obtain ⟨UW, W, hKW, e, hMax⟩ :=
    regularGlobal_exists_maximal_extension F
      (FiniteGlobalAllowed K) hRegular idA
      ⟨hA, inferInstance⟩
  letI : Finite UW := hKW.2
  let root : Structure.Embedding A W := e.comp idA
  exact ⟨globalCanonicalInducedTrace F root,
    globalCanonicalInducedTrace_shadow F root,
    globalCanonicalInducedTrace_mem_maximalAge F K
      root hKW.1 hMax⟩

/-- The reverse reduct direction requires ONLY that the native
class K is hereditary under FULL old functional embeddings.
It is independent of regularity, AP, JEP or Ramsey. -/
theorem globalFiniteMaximalTraceAge_shadow_mem
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A)
    {V : Type}
    {Y : Structure (globalFunctionalPieceLanguage F) V}
    (hY : IsGlobalFiniteMaximalTrace F K Y) :
    K (functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) Y) := by
  rcases hY with
    ⟨_, UW, W, _, hAllowedW, iW, _, _⟩
  exact hHereditary iW hAllowedW

/-- EXACT native reduct of the hereditary finite maximal-trace age,
whenever F is regular and K is full-embedding-hereditary.
Neither the existence direction nor the reverse uses strong AP. -/
theorem globalFiniteMaximalTraceAge_exact_reduct
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A)
    {V : Type} [Finite V] (A : Structure L V) :
    (∃ (Y : Structure (globalFunctionalPieceLanguage F) V),
      functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y = A ∧
      IsGlobalFiniteMaximalTrace F K Y) ↔ K A := by
  constructor
  · rintro ⟨Y, hShadow, hY⟩
    rw [← hShadow]
    exact globalFiniteMaximalTraceAge_shadow_mem
      F K hHereditary hY
  · exact globalFiniteMaximalTraceAge_exists_above
      F K hRegular A

end AllThoseRamseyClasses.Lifts
