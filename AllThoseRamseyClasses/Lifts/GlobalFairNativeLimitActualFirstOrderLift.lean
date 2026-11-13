import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitAllStageCoherentMaps
import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderNativeDecodeIdentity
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFirstOrderDirectLimit
import Mathlib.ModelTheory.DirectLimit

/-!
# Track F: the ACTUAL first-order limit embedding from strict FULL back-and-forth stages

This module finally applies Mathlib's genuine
FirstOrder.Language.DirectLimit.lift to the exact original
first-order function-graph directed system, not to an
invented limit or a different quotient.

The strict coherent FULL native stage maps h_i : X_i ↪ M
were already proved for EVERY original finite fair-chain
index. Encode these maps as first-order relational graph
embeddings and compose with the explicit identity-on-vertices
decoder bridge: the graph structure of the native decoded
limit is propositionally, not definitionally, equivalent to
the quotient's original first-order graph model.

The resulting first-order embedding M ↪ M is a real map
out of Mathlib's original quotient; its canonical stage
equations are consequences of Mathlib's universal property.

The NEXT obligations are surjectivity from the exhaustive
target request schedule and promotion to a native FULL
automorphism via the verified surjective graph-to-FULL
embedding conversion. Neither is assumed in this module.

All statements remain conditional on GlobalOriginalFiniteFraisseInput F,
which retains unresolved general reducible-source shadow
avoidance / original 2019 Claim 2. The numbered manuscript
is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A FULL stage map from an original finite fair-chain
stage to the native limit becomes a genuine first-order
function-graph embedding into the ORIGINAL Mathlib
direct-limit graph model, preserving all relation symbols
and every complete function-graph incidence. -/
noncomputable def globalOriginalFairNativeStrictSequence_firstOrderStageMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i : ℕ) :
    @FirstOrder.Language.Embedding
      (GlobalOriginalTraceFirstOrderLanguage F)
      (GlobalOriginalTraceStageVertex F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) i)
      (GlobalOriginalFairNativeVertex F hInput)
      (globalOriginalTraceStageFirstOrderModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) i)
      (globalOriginalTraceFirstOrderLimitModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)) := by
  let nativeMap :=
    globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule i
  let nativeFO := firstOrderNativeGraphEmbedding nativeMap
  let bridge := firstOrderNativeGraphDecode_id_embedding
    (globalOriginalTraceFirstOrderLimitModel F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput))
  -- Do not use `bridge.comp nativeFO`: the intermediate carrier
  -- is shared, but its two first-order structure instances are
  -- only propositionally equivalent. Assemble the relation law
  -- explicitly using the two separately verified embeddings.
  refine @FirstOrder.Language.Embedding.mk
    (GlobalOriginalTraceFirstOrderLanguage F)
    (GlobalOriginalTraceStageVertex F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput) i)
    (GlobalOriginalFairNativeVertex F hInput)
    (globalOriginalTraceStageFirstOrderModel F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput) i)
    (globalOriginalTraceFirstOrderLimitModel F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput))
    ⟨nativeMap, nativeMap.injective⟩ ?_ ?_
  · intro n sym xs
    exact nomatch sym.down
  · intro n sym xs
    change
      (globalOriginalTraceFirstOrderLimitModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)).RelMap
        sym (nativeMap ∘ xs) ↔
      (globalOriginalTraceStageFirstOrderModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) i).RelMap sym xs
    -- Both FO carrier types coincide, but the intermediate
    -- decoded-graph and quotient model instances do not.
    -- Use the embedding fields with explicit source/target
    -- instances rather than inferred same-carrier instances.
    have hBridge :=
      @FirstOrder.Language.Embedding.map_rel'
        (GlobalOriginalTraceFirstOrderLanguage F)
        (GlobalOriginalFairNativeVertex F hInput)
        (GlobalOriginalFairNativeVertex F hInput)
        (firstOrderNativeGraphStructure
          (globalOriginalActualFairNativeLimit F hInput))
        (globalOriginalTraceFirstOrderLimitModel F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput))
        bridge n sym (nativeMap ∘ xs)
    have hNative :=
      @FirstOrder.Language.Embedding.map_rel'
        (GlobalOriginalTraceFirstOrderLanguage F)
        (GlobalOriginalTraceStageVertex F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput) i)
        (GlobalOriginalFairNativeVertex F hInput)
        (globalOriginalTraceStageFirstOrderModel F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput) i)
        (firstOrderNativeGraphStructure
          (globalOriginalActualFairNativeLimit F hInput))
        nativeFO n sym xs
    have hBridgeIdentity :
        bridge.toFun ∘ (nativeMap ∘ xs) = nativeMap ∘ xs := by
      funext a
      exact firstOrderNativeGraphDecode_id_embedding_apply
        (globalOriginalTraceFirstOrderLimitModel F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput))
        (nativeMap (xs a))
    rw [hBridgeIdentity] at hBridge
    exact hBridge.trans hNative

/-- The underlying vertex map is exactly the existing FULL
native stage map; the relational decoding bridge introduces
no new identification of vertices. -/
theorem globalOriginalFairNativeStrictSequence_firstOrderStageMap_apply
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i : ℕ)
    (a : (globalOriginalActualFairTraceChain F hInput i).Carrier) :
    globalOriginalFairNativeStrictSequence_firstOrderStageMap
      F hInput initial schedule i a =
      globalOriginalFairNativeStrictSequence_allStageMap
        F hInput initial schedule i a := by
  -- The assembled first-order embedding uses exactly the
  -- original FULL vertex map, not a composite through an
  -- ambiguously inferred first-order intermediate instance.
  rfl

/-- The first-order stage maps are compatible with the
EXACT transition maps of the original Mathlib directed system.
This is just the already verified equality of FULL native maps
transported through the faithful complete graph encoding. -/
theorem globalOriginalFairNativeStrictSequence_firstOrderStageMap_comp
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i j : ℕ) (hij : i ≤ j)
    (a : (globalOriginalActualFairTraceChain F hInput i).Carrier) :
    (globalOriginalFairNativeStrictSequence_firstOrderStageMap
      F hInput initial schedule j)
      ((globalOriginalTraceStageFirstOrderMap F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        i j hij) a) =
    (globalOriginalFairNativeStrictSequence_firstOrderStageMap
      F hInput initial schedule i) a := by
  change
    (globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule j)
      ((globalOriginalFiniteTraceChainLE F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        i j hij) a) =
    (globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule i) a
  have h := globalOriginalFairNativeStrictSequence_allStageMap_comp
    F hInput initial schedule i j hij
  exact congrArg
    (fun e : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput i).model
      (globalOriginalActualFairNativeLimit F hInput) => e a) h

/-- The ACTUAL Mathlib first-order directed limit of complete
function graphs embeds into itself via the verified universal
property, using ALL original finite stage maps.

This is an ordinary first-order embedding, not yet an
unconditional native FULL automorphism. -/
noncomputable def globalOriginalFairNativeStrictSequence_firstOrderLimitMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput) :
    @FirstOrder.Language.Embedding
      (GlobalOriginalTraceFirstOrderLanguage F)
      (GlobalOriginalFairNativeVertex F hInput)
      (GlobalOriginalFairNativeVertex F hInput)
      (globalOriginalTraceFirstOrderLimitModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput))
      (globalOriginalTraceFirstOrderLimitModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)) :=
  FirstOrder.Language.DirectLimit.lift
    (GlobalOriginalTraceFirstOrderLanguage F) ℕ
    (fun n : ℕ => GlobalOriginalTraceStageVertex F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput) n)
    (fun i j hij => globalOriginalTraceStageFirstOrderMap F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput) i j hij)
    (globalOriginalFairNativeStrictSequence_firstOrderStageMap
      F hInput initial schedule)
    (globalOriginalFairNativeStrictSequence_firstOrderStageMap_comp
      F hInput initial schedule)

/-- The infinite first-order embedding agrees EXACTLY with
the already constructed FULL native stage map on every
canonical finite-stage inclusion. No arbitrary quotient
representative or new vertex map is introduced. -/
theorem globalOriginalFairNativeStrictSequence_firstOrderLimitMap_of
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i : ℕ)
    (a : (globalOriginalActualFairTraceChain F hInput i).Carrier) :
    globalOriginalFairNativeStrictSequence_firstOrderLimitMap
      F hInput initial schedule
      (globalOriginalTraceFirstOrderLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) i a) =
    globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule i a := by
  change
    (FirstOrder.Language.DirectLimit.lift
      (GlobalOriginalTraceFirstOrderLanguage F) ℕ
      (fun n : ℕ => GlobalOriginalTraceStageVertex F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) n)
      (fun m n h => globalOriginalTraceStageFirstOrderMap F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) m n h)
      (globalOriginalFairNativeStrictSequence_firstOrderStageMap
        F hInput initial schedule)
      (globalOriginalFairNativeStrictSequence_firstOrderStageMap_comp
        F hInput initial schedule))
      (globalOriginalTraceFirstOrderLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) i a) =
      globalOriginalFairNativeStrictSequence_allStageMap
        F hInput initial schedule i a
  -- Compute the two underlying quotient maps directly.
  -- The matching rule `lift_of` is fragile here because
  -- elaboration inserts different semireducible structure
  -- instance arguments for the same original quotient.
  simp only [globalOriginalTraceFirstOrderLimitIncl,
    FirstOrder.Language.DirectLimit.of_apply,
    FirstOrder.Language.DirectLimit.lift_quotient_mk'_sigma_mk']
  exact globalOriginalFairNativeStrictSequence_firstOrderStageMap_apply
    F hInput initial schedule i a

end AllThoseRamseyClasses.Lifts
