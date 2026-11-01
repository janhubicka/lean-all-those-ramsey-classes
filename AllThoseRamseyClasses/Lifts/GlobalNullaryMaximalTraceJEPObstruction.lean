import AllThoseRamseyClasses.Lifts.GlobalNullaryJEPObstruction
import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3ClassAssembly

/-!
# Track F: nullary JEP failure reaches the ACTUAL maximal-trace age

The separately checked native finite counterexample already shows
that two allowed original functional structures with opposite truth
values for a nullary relation have no common FULL native target.
To audit the printed Section 3 `mainthm` itself, it is important
to show that its ACTUAL maximal-trace age cannot regain JEP by adding
piece-class relations.

For any regular F and full-hereditary native class K, JEP of the
actual original maximal-trace age would force native JEP:
  1. expand both finite K-members to genuine maximal traces;
  2. jointly embed those traces into one allowed expanded trace;
  3. forget added piece predicates using FULL shadow embeddings;
  4. use true hereditary membership to see its native shadow lies in K.

For F = empty, regularity is vacuous because there are NO genuine
forbidden pieces, at any root width. Hence any zero-arity old
relation symbol gives an ACTUAL counterexample to the full maximal
age JEP, not only to a suggested intermediate native-JEP lemma.

This does NOT refute Section 3 under a convention requiring
strictly positive relation/function arities. Review-only TODO
ATRC-073 records that editorial choice. No frozen prose changes.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Full joint embedding of the original hereditary maximal-trace
age forces FULL joint embedding of the underlying native class K.
This is a converse to the earlier JEP transfer, under regularity
and genuine native full-embedding heredity of K. -/
theorem globalFiniteMaximalTrace_core_implies_nativeJEP
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A)
    (hCore : GlobalFiniteMaximalTraceAmalgamationCore F K) :
    GlobalNativeFiniteJEP K := by
  intro UA UB A B hFinA hFinB hKA hKB
  letI : Finite UA := hFinA
  letI : Finite UB := hFinB
  obtain ⟨Y, hShadowY, hY⟩ :=
    globalFiniteMaximalTraceAge_exists_above
      F K hRegular A hKA
  obtain ⟨Z, hShadowZ, hZ⟩ :=
    globalFiniteMaximalTraceAge_exists_above
      F K hRegular B hKB
  obtain ⟨UT, T, hT, jY, jZ, _⟩ :=
    hCore.jointEmbedding Y Z hY hZ
  let C : Structure L UT :=
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) T
  have hKC : K C :=
    globalFiniteMaximalTraceAge_shadow_mem
      F K hHereditary hT
  let eA : Structure.Embedding A C := by
    rw [← hShadowY]
    exact functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) jY
  let eB : Structure.Embedding B C := by
    rw [← hShadowZ]
    exact functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) jZ
  exact ⟨UT, C, hT.1, hKC, eA, eB, True.intro⟩

/-- The truly EMPTY forbidden family has NO selected geometric
pieces: each such piece would contain a forbidden witness, whose
family-membership assertion is False. Thus the actual original
root-injective global piece-class quotient is finite at every
positive width (indeed empty), and F=empty is regular. -/
theorem emptyGlobalForbiddenFamily_regular
    (L : Language.{u}) :
    GlobalFunctionalPieceRegular (emptyGlobalForbiddenFamily L) := by
  intro n _hn
  letI : IsEmpty
      (SelectedFunctionalChart (emptyGlobalForbiddenFamily L) n) :=
    ⟨by
      intro P
      have hp : IsForbiddenGeometricFunctionalPiece
          (emptyGlobalForbiddenFamily L) P.1.pattern := P.2
      obtain ⟨W, A, _hFinite, hF, d, _hIso⟩ := hp
      exact hF⟩
  infer_instance

/-- With one genuine old NULLARY relation symbol, the ACTUAL
hereditary regular original maximal global-lift age for the
empty forbidden family is NOT a finite-age amalgamation core:
even its joint-embedding axiom fails under FULL embeddings.

The empty family is explicitly proved regular above; this
counterexample does not hide regularity as an extra hypothesis.
It isolates the language-arity convention of the printed theorem,
not an issue with the corrected 2019 relational Ramsey theorem. -/
theorem emptyForbidden_globalMaximalTraceCore_notJEP_of_nullaryRelation
    (L : Language.{u}) (R : L.RelSymbol)
    (hZero : L.relArity R = 0) :
    ¬ GlobalFiniteMaximalTraceAmalgamationCore
      (emptyGlobalForbiddenFamily L)
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) := by
  intro hCore
  have hNative :
      GlobalNativeFiniteJEP
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) :=
    globalFiniteMaximalTrace_core_implies_nativeJEP
      (emptyGlobalForbiddenFamily L)
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A)
      (emptyGlobalForbiddenFamily_regular L)
      (fun e hB =>
        avoidsGlobalFunctionalEHN_of_embedding
          (emptyGlobalForbiddenFamily L) e hB)
      hCore
  exact (emptyForbidden_nativeJEP_fails_of_nullaryRelation
    L R hZero) hNative

end AllThoseRamseyClasses.Lifts
