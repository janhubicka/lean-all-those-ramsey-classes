import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteListStage
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteExtension
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFullLimitCocone

/-!
# Track F: strict growth in finite-batch FULL back-and-forth

The finite-list two-sided extension theorem need not increase the
underlying finite-stage index. This is sufficient for finite
coverage, but NOT by itself enough for a selected chain of
stages to be cofinal in the original ℕ-indexed fair system.

To enforce the missing rank/index cofinality, first meet the
finite request list at some actual stage n, and then use the
verified native finite FULL age-extension property to extend
that entire stage map along the TRUE successor transition
X_n ↪ X_(n+1). This preserves ALL earlier source/target
coverage, by the full cocone identity and genuine FULL map
compatibility. The final stage index is > the original index.

The proof works even for the empty request list or an empty
native limit: it does not postulate an arbitrary vertex to
force growth. This is the strict-step interface needed for
a countable cofinal stage recursion and Mathlib's actual
direct-limit universal property.

Conditional on GlobalOriginalFiniteFraisseInput, including
the unresolved general reducible-source shadow-avoidance /
Claim 2 premise. Frozen numbered manuscript unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A simultaneous finite-list FULL source-cover/target-hit
extension can always be chosen at a STRICTLY later stage.
The strictness is obtained by one genuine full successor
extension, not by assuming new vertices exist. -/
theorem globalOriginalActualFairNativeLimit_finiteList_strictStage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (pairs : List
      ((GlobalOriginalTraceFirstOrderDirectLimit F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput)) ×
       (GlobalOriginalTraceFirstOrderDirectLimit F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput))))
    (m : ℕ)
    (f : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairNativeLimit F hInput)) :
    ∃ (n : ℕ) (hmn : m ≤ n),
      m < n ∧
      ∃ (g : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput n).model
        (globalOriginalActualFairNativeLimit F hInput)),
        (∀ p ∈ pairs,
          ∃ (a b : (globalOriginalActualFairTraceChain F hInput n).Carrier),
            (globalOriginalTraceFullLimitIncl F hInput
              (globalOriginalRepresentativePrefix F hInput)
              (globalOriginalExtensionDiagramPrefix F hInput)
              n) a = p.1 ∧ g b = p.2) ∧
        ∀ a : (globalOriginalActualFairTraceChain F hInput m).Carrier,
          g ((globalOriginalFiniteTraceChainLE F hInput
            (globalOriginalRepresentativePrefix F hInput)
            (globalOriginalExtensionDiagramPrefix F hInput)
            m n hmn) a) = f a := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨k, hmk, gk, hkCover, hkCompat⟩ :=
    globalOriginalActualFairNativeLimit_finiteList_twoSided_stage
      F hInput pairs m f
  have hStep : k ≤ k + 1 := Nat.le_succ k
  let ek := globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams k (k + 1) hStep
  letI : Finite (globalOriginalActualFairTraceChain F hInput k).Carrier :=
    (globalOriginalActualFairTraceChain F hInput k).member.1
  have hAge :
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C)
        (globalOriginalActualFairTraceChain F hInput (k + 1)).model :=
    (globalOriginalActualFairTraceChain F hInput (k + 1)).member
  obtain ⟨g, hg⟩ :=
    globalOriginalActualFairNativeLimit_extend_fullAgeDiagram
      F hInput
      (globalOriginalActualFairTraceChain F hInput k).model
      (globalOriginalActualFairTraceChain F hInput (k + 1)).model
      hAge ek gk
  have hmn : m ≤ k + 1 := Nat.le_succ_of_le hmk
  have hstrict : m < k + 1 := Nat.lt_succ_of_le hmk
  refine ⟨k + 1, hmn, hstrict, g, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, b, ha, hb⟩ := hkCover p hp
    refine ⟨ek a, ek b, ?_, ?_⟩
    · have hcocone :=
        globalOriginalTraceFullLimitIncl_comp F hInput
          representatives diagrams k (k + 1) hStep
      have hp :=
        congrArg
          (fun e : Structure.Embedding
            (globalOriginalActualFairTraceChain F hInput k).model
            (globalOriginalActualFairNativeLimit F hInput) => e a)
          hcocone
      exact hp.trans ha
    · exact (hg b).trans hb
  · intro a
    have hcomp :=
      congrArg
        (fun e : Structure.Embedding
          (globalOriginalActualFairTraceChain F hInput m).model
          (globalOriginalActualFairTraceChain F hInput (k + 1)).model =>
            e a)
        (globalOriginalFiniteTraceChainLE_comp F hInput
          representatives diagrams m k (k + 1) hmk hStep)
    calc
      g ((globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams m (k + 1) hmn) a) =
        g (ek ((globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams m k hmk) a)) :=
          congrArg g hcomp.symm
      _ = gk ((globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams m k hmk) a) :=
          hg ((globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams m k hmk) a)
      _ = f a := hkCompat a

end AllThoseRamseyClasses.Lifts
