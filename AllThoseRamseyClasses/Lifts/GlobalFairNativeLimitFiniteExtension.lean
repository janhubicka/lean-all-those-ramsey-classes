import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceLimitFiniteFullFactor
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFullLimitCocone
import AllThoseRamseyClasses.Lifts.GlobalActualFairFraisseFiniteExtension
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainCoherence

/-!
# Track F: actual FULL finite-extension property in the native fair limit

The full decoded limit is no longer merely a first-order graph limit.
For any finite FULL age diagram A ↪ B, every FULL A-copy in the
actual native fair limit extends to a FULL B-copy there.

The proof first factors the finite A-copy through one genuine finite
stage (finite FULL factorization), uses the already verified fair
finite-stage arbitrary-diagram extension theorem, and maps the
resulting B-copy back into the native limit. The FULL cocone equation
ensures that the new copy agrees with the original A-copy pointwise.

This is conditional on GlobalOriginalFiniteFraisseInput F, which for
general reducible source families still includes the outstanding
shadow-free-amalgamation assumption. No unrestricted 2019 theorem
or back-and-forth/ultrahomogeneity is asserted here.

The numbered 2019 manuscript remains unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every FULL embedding of a finite original-age structure A into
the ACTUAL native fair limit extends along any FULL original-age
embedding A ↪ B.  The witness is a FULL functional embedding of B,
not merely a first-order relational or weak functional map. -/
theorem globalOriginalActualFairNativeLimit_extend_fullAgeDiagram
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VA VB : Type} [Finite VA]
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (hB : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) B)
    (i : Structure.Embedding A B)
    (f : Structure.Embedding A
      (globalOriginalActualFairNativeLimit F hInput)) :
    ∃ (g : Structure.Embedding B
      (globalOriginalActualFairNativeLimit F hInput)),
      ∀ x : VA, g (i x) = f x := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨m, fStage, hfStage⟩ :=
    globalOriginalTraceNativeLimit_finiteFullFactor
      F hInput representatives diagrams A f
  obtain ⟨n, hmn, g, hg⟩ :=
    globalOriginalActualFairTraceChain_extend_arbitraryFullAgeDiagram
      F hInput A B hB i m fStage
  let um := globalOriginalTraceFullLimitIncl
    F hInput representatives diagrams m
  let un1 := globalOriginalTraceFullLimitIncl
    F hInput representatives diagrams (n + 1)
  refine ⟨un1.comp g, ?_⟩
  intro x
  have hCocone :
      un1 ((globalOriginalActualFairTraceChainStep F hInput n)
        ((globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams m n hmn) (fStage x))) =
      um (fStage x) := by
    have hpoint :=
      congrArg
        (fun e : Structure.Embedding
          (globalOriginalFiniteTraceChain
            F hInput representatives diagrams m).model
          (globalOriginalTraceNativeDirectLimitModel
            F hInput representatives diagrams) => e (fStage x))
        (globalOriginalTraceFullLimitIncl_comp
          F hInput representatives diagrams m (n + 1)
            (Nat.le_succ_of_le hmn))
    rw [globalOriginalFiniteTraceChainLE_succ
      F hInput representatives diagrams m n hmn] at hpoint
    exact hpoint
  calc
    (un1.comp g) (i x) = un1 (g (i x)) := rfl
    _ = un1 ((globalOriginalActualFairTraceChainStep F hInput n)
          ((globalOriginalFiniteTraceChainLE
            F hInput representatives diagrams m n hmn) (fStage x))) := by
          exact congrArg un1 (hg x)
    _ = um (fStage x) := hCocone
    _ = f x := hfStage x

end AllThoseRamseyClasses.Lifts
