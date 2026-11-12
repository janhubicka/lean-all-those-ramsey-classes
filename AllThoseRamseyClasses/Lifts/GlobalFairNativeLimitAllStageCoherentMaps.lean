import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStrictStageCoherence
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainCoherence

/-!
# Track F: compatible FULL maps from EVERY original finite fair stage

The strictly increasing proof-carrying selected-stage sequence
supplies FULL maps g_n:X_(m_n) ↪ M with m_n ≥ n and coherence
along all selected stages. Hence every ORIGINAL fair-chain
stage X_i has a canonical FULL transition X_i ↪ X_(m_i).
Compose it with the chosen FULL map g_i to obtain a genuine
FULL embedding h_i:X_i ↪ M.

The key theorem proves these h_i are coherent with the
ORIGINAL directed system, not merely the chosen subchain:
h_j ∘ e_(i,j) = h_i whenever i≤j. This is exactly the
full stage-level compatibility needed for Mathlib's actual
FirstOrder.Language.DirectLimit.lift after graph encoding.

The proof relies on the TWO genuine all-stage FULL transition
composition equalities and the existing full selected-stage
coherence, without treating the direct-limit quotient as
an assumed Fraïssé limit. No infinite map or automorphism
is asserted in this module.

All results remain conditional on GlobalOriginalFiniteFraisseInput
and its unresolved general reducible-source shadow-avoidance /
2019 Claim 2 obligation. Numbered manuscript unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For any original fair-chain index i, extend along its
canonical FULL transition to the chosen strict-stage index
m_i and then use the chosen FULL stage map into M.
The bound i≤m_i was formally proved by strict growth. -/
noncomputable def globalOriginalFairNativeStrictSequence_allStageMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i : ℕ) :
    Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput i).model
      (globalOriginalActualFairNativeLimit F hInput) :=
  let seq := globalOriginalFairNativeStrictStageSequence
    F hInput initial schedule
  (seq i).2.comp
    (globalOriginalFiniteTraceChainLE F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput)
      i (seq i).1
      (globalOriginalFairNativeStrictStageSequence_index_ge
        F hInput initial schedule i))

/-- The new FULL map is literally the specified composite of
the original stage transition with the FULL selected-stage map;
its vertex function is unchanged. -/
theorem globalOriginalFairNativeStrictSequence_allStageMap_apply
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i : ℕ)
    (a : (globalOriginalActualFairTraceChain F hInput i).Carrier) :
    globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule i a =
    (globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule i).2
      ((globalOriginalFiniteTraceChainLE F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        i (globalOriginalFairNativeStrictStageSequence
          F hInput initial schedule i).1
        (globalOriginalFairNativeStrictStageSequence_index_ge
          F hInput initial schedule i)) a) := by
  rfl

/-- Crucial universal-property interface: the FULL maps
h_i:X_i↪M are coherent along EVERY transition of the original
finite fair chain, not only along the chosen subchain.

This equality is in Structure.Embedding, so it preserves
complete partial/multivalued function fibres and reflects
all old and newly added relations. -/
theorem globalOriginalFairNativeStrictSequence_allStageMap_comp
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i j : ℕ) (hij : i ≤ j) :
    (globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule j).comp
      (globalOriginalFiniteTraceChainLE F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        i j hij) =
    globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule i := by
  classical
  apply Structure.Embedding.ext
  intro a
  let seq := globalOriginalFairNativeStrictStageSequence
    F hInput initial schedule
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  let hii : i ≤ (seq i).1 :=
    globalOriginalFairNativeStrictStageSequence_index_ge
      F hInput initial schedule i
  let hjj : j ≤ (seq j).1 :=
    globalOriginalFairNativeStrictStageSequence_index_ge
      F hInput initial schedule j
  obtain ⟨hlevels, hSeq⟩ :=
    globalOriginalFairNativeStrictStageSequence_coherent
      F hInput initial schedule i j hij
  have hcomp1 :=
    congrArg
      (fun e : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput i).model
        (globalOriginalActualFairTraceChain F hInput (seq j).1).model =>
          e a)
      (globalOriginalFiniteTraceChainLE_comp F hInput
        representatives diagrams i j (seq j).1 hij hjj)
  have hcomp2 :=
    congrArg
      (fun e : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput i).model
        (globalOriginalActualFairTraceChain F hInput (seq j).1).model =>
          e a)
      (globalOriginalFiniteTraceChainLE_comp F hInput
        representatives diagrams i (seq i).1 (seq j).1 hii hlevels)
  calc
    ((globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule j).comp
        (globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams i j hij)) a =
      (seq j).2
        ((globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams j (seq j).1 hjj)
          ((globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams i j hij) a)) := rfl
    _ = (seq j).2
          ((globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams i (seq j).1
            (le_trans hij hjj)) a) :=
        congrArg (seq j).2 hcomp1
    _ = (seq j).2
          ((globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams (seq i).1 (seq j).1 hlevels)
            ((globalOriginalFiniteTraceChainLE F hInput
              representatives diagrams i (seq i).1 hii) a)) :=
        congrArg (seq j).2 hcomp2.symm
    _ = (seq i).2
          ((globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams i (seq i).1 hii) a) :=
        hSeq _
    _ = (globalOriginalFairNativeStrictSequence_allStageMap
          F hInput initial schedule i) a := rfl

end AllThoseRamseyClasses.Lifts
