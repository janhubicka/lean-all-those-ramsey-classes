import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteExtension
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainAllStages

/-!
# Track F: extend arbitrary FULL limit embeddings to any later fair stage

The native fair-limit finite FULL age extension theorem already
extends any finite-age arrow i:A↪B along an arbitrary FULL map
f:A↪M. Specialize this to the **actual canonical FULL stage
transitions** e_(m,n):X_m↪X_n. Thus any FULL embedding of an
original finite stage X_m into the actual native limit extends
to EVERY prescribed later stage X_n, not merely some later
stage chosen by a fair-extension argument.

In particular one can demand strict growth of the selected
stage indices in the countable back-and-forth recursion, e.g.
by requiring the next index be at least the previous plus one.
This is essential to make the chosen indices cofinal in ℕ
before applying the genuine first-order directed-limit lift.

This is conditional on GlobalOriginalFiniteFraisseInput F.
No unrestricted reducible-source shadow-avoidance/Claim 2,
ultrahomogeneity, or full 2019 Ramsey conclusion is asserted.
The numbered manuscript is untouched.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every FULL map of a finite fair stage into the actual
native limit can be extended along the canonical FULL
transition to ANY specified later stage, with exact
pointwise agreement. -/
theorem globalOriginalActualFairNativeLimit_extend_to_laterStage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (m n : ℕ) (hmn : m ≤ n)
    (f : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairNativeLimit F hInput)) :
    ∃ (g : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput n).model
      (globalOriginalActualFairNativeLimit F hInput)),
      ∀ a : (globalOriginalActualFairTraceChain F hInput m).Carrier,
        g ((globalOriginalFiniteTraceChainLE F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput)
          m n hmn) a) = f a := by
  classical
  letI : Finite (globalOriginalActualFairTraceChain F hInput m).Carrier :=
    (globalOriginalActualFairTraceChain F hInput m).member.1
  have hAge :
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C)
        (globalOriginalActualFairTraceChain F hInput n).model :=
    (globalOriginalActualFairTraceChain F hInput n).member
  exact globalOriginalActualFairNativeLimit_extend_fullAgeDiagram
    F hInput
    (globalOriginalActualFairTraceChain F hInput m).model
    (globalOriginalActualFairTraceChain F hInput n).model
    hAge
    (globalOriginalFiniteTraceChainLE F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput)
      m n hmn)
    f

end AllThoseRamseyClasses.Lifts
