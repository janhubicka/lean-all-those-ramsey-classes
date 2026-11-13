import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFirstOrderSurjectivity
import AllThoseRamseyClasses.Lifts.GlobalFraisseSurjectiveFirstOrderNativeSelfMap
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitSelectedStageEquality
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitTwoCopyAlignment

/-!
# Track F: conditional finite FULL ultrahomogeneity of the ACTUAL native fair limit

This is the final assembly of the previously isolated Track F
proof ingredients, not an invocation of an assumed Fraïssé
limit, a new complete-graph quotient or Mathlib's ordinary
relational ultrahomogeneity theorem.

Given two FULL embeddings of a FINITE native age member A
into the actual decoded native fair limit M, we:

1. Use actual finite FULL factorization and age extension to
   align the two A-copies on a common genuine finite stage
   X_m, represented by i:A↪X_m and g:X_m↪M with
   u_m∘i=j₀ and g∘i=j₁.
2. Start the STRICT proof-carrying countable FULL stage
   recursion with initial state (m,g) and the exhaustive
   optional diagonal request schedule on M.
3. Use the certified all-original-stage coherence to apply
   the genuine Mathlib first-order directed-limit universal
   property. Every target vertex is reached, so the resulting
   first-order self-embedding of the ORIGINAL graph quotient
   is a bijection.
4. Transport this self-embedding along the explicit identity
   first-order EQUIVALENCE between the original function-graph
   quotient model and the complete graph of its native decoder.
   The surjective graph-to-FULL bridge reconstructs a genuine
   FULL native self-embedding of M with an actual FULL inverse.
5. The exact lift_of law and selected-stage initial equality
   show this automorphism sends every j₀(a) to j₁(a).

The result is precise FINITE FULL homogeneity of the actual
locally-finite native structure. No function-output value
is clipped or dropped, including partial, nullary and
multi-valued fibres, and all old/new relations are reflected.

IMPORTANT BOUNDARY: the theorem is CONDITIONAL on the original
GlobalOriginalFiniteFraisseInput F, which for arbitrary reducible
forbidden-source families still includes the unresolved global
shadow-avoidance / 2019 Claim 2 hypothesis. It does NOT by
itself repair the unconditional published theorem or prove
the full Ramsey class statement. The numbered manuscript
remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any two genuine FULL finite native age embeddings into
the ACTUAL fair decoded native limit are conjugate by a
BIJECTIVE FULL native self-embedding.

Both the embedding and its existence are constructed from
the actual fair chain, Mathlib's directed-limit quotient and
the entire complete function-graph encoding. No arbitrary
first-order relational subset is treated as function-closed.

This is conditional on the original finite age Fraïssé input,
not on a new homogeneity/existence postulate. -/
theorem globalOriginalActualFairNativeLimit_finiteFullHomogeneous
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {V : Type} [Finite V]
    (A : Structure (globalFunctionalPieceLanguage F) V)
    (j₀ j₁ : Structure.Embedding A
      (globalOriginalActualFairNativeLimit F hInput)) :
    ∃ (aut : Structure.Embedding
      (globalOriginalActualFairNativeLimit F hInput)
      (globalOriginalActualFairNativeLimit F hInput)),
      Function.Bijective aut ∧
      ∀ v : V, aut (j₀ v) = j₁ v := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨m, i, g, hFirst, hSecond⟩ :=
    globalOriginalActualFairNativeLimit_twoFullCopies_alignStage
      F hInput A j₀ j₁
  let initial : GlobalOriginalFairNativeStageState F hInput := ⟨m, g⟩
  let schedule : ℕ → GlobalOriginalFairNativeRequests F hInput :=
    globalOriginalFairNativeDiagonalSchedule F hInput
  let hFO : (GlobalOriginalTraceFirstOrderLanguage F).Structure
      (GlobalOriginalFairNativeVertex F hInput) :=
    globalOriginalTraceFirstOrderLimitModel F hInput
      representatives diagrams
  let eFO := globalOriginalFairNativeStrictSequence_firstOrderLimitMap
    F hInput initial schedule
  have heFO : Function.Surjective eFO :=
    globalOriginalFairNativeStrictSequence_firstOrderLimitMap_surjective_of_diagonal
      F hInput initial schedule
      (globalOriginalFairNativeDiagonalSchedule_covers F hInput)
  let aut : Structure.Embedding
      (globalOriginalActualFairNativeLimit F hInput)
      (globalOriginalActualFairNativeLimit F hInput) :=
    firstOrderNativeGraphDecode_surjectiveSelf_toFull hFO eFO heFO
  have hOnto : Function.Surjective aut :=
    firstOrderNativeGraphDecode_surjectiveSelf_toFull_surjective hFO eFO heFO
  have hAutApply
      (x : GlobalOriginalFairNativeVertex F hInput) :
      aut x = eFO x :=
    firstOrderNativeGraphDecode_surjectiveSelf_toFull_apply
      hFO eFO heFO x
  refine ⟨aut, ⟨aut.injective, hOnto⟩, ?_⟩
  intro v
  have hStage :
      eFO (globalOriginalTraceFirstOrderLimitIncl F hInput
        representatives diagrams m (i v)) = g (i v) := by
    calc
      eFO (globalOriginalTraceFirstOrderLimitIncl F hInput
          representatives diagrams m (i v)) =
        (globalOriginalFairNativeStrictSequence_allStageMap
          F hInput initial schedule m) (i v) :=
        globalOriginalFairNativeStrictSequence_firstOrderLimitMap_of
          F hInput initial schedule m (i v)
      _ = g (i v) :=
        globalOriginalFairNativeStrictSequence_allStageMap_initial
          F hInput initial schedule (i v)
  calc
    aut (j₀ v) =
        aut ((globalOriginalTraceFullLimitIncl F hInput
          representatives diagrams m) (i v)) := by
          rw [hFirst v]
    _ = eFO ((globalOriginalTraceFullLimitIncl F hInput
          representatives diagrams m) (i v)) := hAutApply _
    _ = eFO (globalOriginalTraceFirstOrderLimitIncl F hInput
          representatives diagrams m (i v)) := by
          rfl
    _ = g (i v) := hStage
    _ = j₁ v := hSecond v

/-- The finite FULL homogeneity certificate admits a
genuine FULL inverse embedding, preserving every exact
function-value fibre in both directions.

In particular this is a native functional automorphism,
not a merely set-theoretic bijection of vertices. -/
theorem globalOriginalActualFairNativeLimit_finiteFullHomogeneous_withInverse
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {V : Type} [Finite V]
    (A : Structure (globalFunctionalPieceLanguage F) V)
    (j₀ j₁ : Structure.Embedding A
      (globalOriginalActualFairNativeLimit F hInput)) :
    ∃ (aut inv : Structure.Embedding
      (globalOriginalActualFairNativeLimit F hInput)
      (globalOriginalActualFairNativeLimit F hInput)),
      (∀ x, aut (inv x) = x) ∧
      (∀ x, inv (aut x) = x) ∧
      (∀ v : V, aut (j₀ v) = j₁ v) := by
  obtain ⟨aut, ⟨hinj, hsurj⟩, hcopy⟩ :=
    globalOriginalActualFairNativeLimit_finiteFullHomogeneous
      F hInput A j₀ j₁
  let inv := fullEmbeddingInverseOfSurjective aut hsurj
  refine ⟨aut, inv, ?_, ?_, hcopy⟩
  · intro x
    exact fullEmbeddingInverseOfSurjective_rightInverse
      aut hsurj x
  · intro x
    apply hinj
    exact fullEmbeddingInverseOfSurjective_rightInverse
      aut hsurj (aut x)

end AllThoseRamseyClasses.Lifts
