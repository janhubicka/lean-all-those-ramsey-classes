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

/-- The EXACT standalone joint-embedding property of the original
finite hereditary maximal-trace age. Neither HP nor strong AP is
included here. This keeps the nullary counterexample targeted at
JOINT EMBEDDING itself, rather than failure of a larger conjunction. -/
def GlobalFiniteMaximalTraceAgeJEP
    (F K : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {VY VZ : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ),
    IsGlobalFiniteMaximalTrace F K Y →
    IsGlobalFiniteMaximalTrace F K Z →
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F K T ∧
      ∃ (_jY : Structure.Embedding Y T)
        (_jZ : Structure.Embedding Z T), True

/-- The genuine maximal-trace JEP already forces native JEP under
regularity and native full-embedding heredity. Strong AP is neither
a hypothesis nor used in this proof. -/
theorem globalFiniteMaximalTrace_jep_implies_nativeJEP
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A)
    (hJEP : GlobalFiniteMaximalTraceAgeJEP F K) :
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
    hJEP Y Z hY hZ
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

/-- The exact original maximal-trace JEP is EQUIVALENT to the
full native JEP of K, under global regularity and full heredity of K.
The reverse implication is the previously verified JEP transfer.
No shadow-free amalgamation or Claim 2 is required. -/
theorem globalFiniteMaximalTraceAge_JEP_iff_nativeJEP
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A) :
    GlobalFiniteMaximalTraceAgeJEP F K ↔
      GlobalNativeFiniteJEP K := by
  constructor
  · exact globalFiniteMaximalTrace_jep_implies_nativeJEP
      F K hRegular hHereditary
  · intro hNative VY VZ Y Z hY hZ
    exact globalFiniteMaximalTraceAge_JEP_of_nativeJEP
      F K hRegular hNative Y Z hY hZ

/-- The earlier stronger bundled-core consequence remains available,
but now transparently factors through only its JEP field. -/
theorem globalFiniteMaximalTrace_core_implies_nativeJEP
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A)
    (hCore : GlobalFiniteMaximalTraceAmalgamationCore F K) :
    GlobalNativeFiniteJEP K :=
  globalFiniteMaximalTrace_jep_implies_nativeJEP
    F K hRegular hHereditary hCore.jointEmbedding

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

/-- For a regular empty forbidden family, ONE old nullary
relation obstructs JOINT EMBEDDING of the actual original global
maximal-trace age. The conclusion concerns the JEP itself, not
a bundled conjunction involving hereditary or strong AP.

The proof uses the full native JEP equivalence and a literal finite
counterexample. It applies only if arity-zero symbols are admitted
by the language convention. -/
theorem emptyForbidden_globalMaximalTraceAgeJEP_fails_of_nullaryRelation
    (L : Language.{u}) (R : L.RelSymbol)
    (hZero : L.relArity R = 0) :
    ¬ GlobalFiniteMaximalTraceAgeJEP
      (emptyGlobalForbiddenFamily L)
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) := by
  intro hJEP
  have hNative :
      GlobalNativeFiniteJEP
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) :=
    globalFiniteMaximalTrace_jep_implies_nativeJEP
      (emptyGlobalForbiddenFamily L)
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A)
      (emptyGlobalForbiddenFamily_regular L)
      (fun e hB =>
        avoidsGlobalFunctionalEHN_of_embedding
          (emptyGlobalForbiddenFamily L) e hB)
      hJEP
  exact (emptyForbidden_nativeJEP_fails_of_nullaryRelation
    L R hZero) hNative

/-- The bundled HP/JEP/strong-AP age core fails as an immediate
corollary of the stronger standalone JEP obstruction above. -/
theorem emptyForbidden_globalMaximalTraceCore_notJEP_of_nullaryRelation
    (L : Language.{u}) (R : L.RelSymbol)
    (hZero : L.relArity R = 0) :
    ¬ GlobalFiniteMaximalTraceAmalgamationCore
      (emptyGlobalForbiddenFamily L)
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) := by
  intro hCore
  exact (emptyForbidden_globalMaximalTraceAgeJEP_fails_of_nullaryRelation
    L R hZero) hCore.jointEmbedding

end AllThoseRamseyClasses.Lifts
