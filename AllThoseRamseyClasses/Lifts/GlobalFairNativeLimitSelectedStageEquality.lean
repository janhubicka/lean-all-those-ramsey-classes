import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitAllStageCoherentMaps

/-!
# Track F: original-stage maps recover each selected FULL stage map

The strict back-and-forth recursion chooses FULL maps
g_n : X_(m_n) ↪ M at selected fair-chain levels m_n.
To invoke the actual first-order direct-limit universal
property, we previously constructed maps h_i:X_i↪M
from ALL original stage indices i.

This module proves the exact comparison that the stage
maps used by the infinite quotient lift agree with the
original selected FULL map on its own selected stage:
h_(m_n)=g_n pointwise on X_(m_n).

The key subtlety is that m_n is a *stage index* while n is
an *iteration index*. We use the verified inequality
n≤m_n and selected-sequence coherence across ITERATIONS
n and m_n. Both of their FULL stage maps act on exactly
the same actual underlying finite carrier X_(m_n).

The specialization n=0 recovers the original arbitrary
initial FULL finite-stage map, ensuring that a later
automorphism can extend the originally prescribed finite
partial isomorphism.

No infinite map, surjectivity or homogeneity is postulated.
Original finite Fraïssé input remains explicit with its
open unrestricted reducible-source shadow avoidance/Claim 2.
Numbered manuscript unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- On EVERY selected finite stage X_(m_n), the genuine FULL
original-indexed map h_(m_n) equals the chosen FULL stage
map g_n pointwise. The proof is based on coherent selected
stage transitions, not on a quotient identification. -/
theorem globalOriginalFairNativeStrictSequence_allStageMap_selected
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (n : ℕ)
    (a : (globalOriginalActualFairTraceChain F hInput
      (globalOriginalFairNativeStrictStageSequence
        F hInput initial schedule n).1).Carrier) :
    globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule
      (globalOriginalFairNativeStrictStageSequence
        F hInput initial schedule n).1 a =
    (globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule n).2 a := by
  classical
  let seq := globalOriginalFairNativeStrictStageSequence
    F hInput initial schedule
  have hn :
      n ≤ (seq n).1 :=
    globalOriginalFairNativeStrictStageSequence_index_ge
      F hInput initial schedule n
  obtain ⟨hle, hcompat⟩ :=
    globalOriginalFairNativeStrictStageSequence_coherent
      F hInput initial schedule n (seq n).1 hn
  rw [globalOriginalFairNativeStrictSequence_allStageMap_apply]
  exact hcompat a

/-- At the original index of the initial finite stage,
the all-stage FULL map recovers EXACTLY the initially chosen
FULL embedding, not merely a copy with the same age. -/
theorem globalOriginalFairNativeStrictSequence_allStageMap_initial
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (a : (globalOriginalActualFairTraceChain F hInput initial.1).Carrier) :
    globalOriginalFairNativeStrictSequence_allStageMap
      F hInput initial schedule initial.1 a = initial.2 a := by
  simpa only [globalOriginalFairNativeStrictStageSequence_zero]
    using globalOriginalFairNativeStrictSequence_allStageMap_selected
      F hInput initial schedule 0 a

end AllThoseRamseyClasses.Lifts
