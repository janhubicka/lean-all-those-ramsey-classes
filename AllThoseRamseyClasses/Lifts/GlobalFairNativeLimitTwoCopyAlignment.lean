import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteExtension
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceLimitFiniteFullFactor

/-!
# Track F: align two finite FULL copies through one actual fair stage

Given any finite FULL structure A with two FULL embeddings j₀,j₁
into the actual native fair direct limit, choose a genuine fair
stage X_n and a FULL embedding i:A↪X_n whose canonical limit
inclusion recovers j₀. Then the verified finite FULL limit
extension theorem lifts j₁ along i to a genuine FULL
g:X_n↪M.

The two copies of A now have a common finite-stage domain:
u_n ∘ i = j₀ and g ∘ i = j₁ pointwise. This is the precise
initial condition for native functional back-and-forth.

No assumption that ordinary finite relational subsets are
function-closed is used. All old/new relations and complete
partial/multivalued function-value fibres are preserved.
Conditional on GlobalOriginalFiniteFraisseInput F, which still
requires the unresolved unrestricted original shadow-avoidance
premise for general reducible forbidden sources. The numbered
2019 manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any two genuine FULL embeddings of a finite native structure
into the actual fair limit are represented on a shared genuine
finite-age stage: the first is the canonical stage inclusion,
and the second extends to a FULL embedding of that whole stage.

This is exactly the initial finite diagram for an alternating
native back-and-forth construction. -/
theorem globalOriginalActualFairNativeLimit_twoFullCopies_alignStage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {V : Type} [Finite V]
    (A : Structure (globalFunctionalPieceLanguage F) V)
    (j₀ j₁ : Structure.Embedding A
      (globalOriginalActualFairNativeLimit F hInput)) :
    ∃ (n : ℕ)
      (i : Structure.Embedding A
        (globalOriginalActualFairTraceChain F hInput n).model)
      (g : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput n).model
        (globalOriginalActualFairNativeLimit F hInput)),
      (∀ v : V,
        (globalOriginalTraceFullLimitIncl F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput) n)
          (i v) = j₀ v) ∧
      (∀ v : V, g (i v) = j₁ v) := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨n, i, hi⟩ :=
    globalOriginalTraceNativeLimit_finiteFullFactor
      F hInput representatives diagrams A j₀
  have hAge :
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C)
        (globalOriginalActualFairTraceChain F hInput n).model :=
    (globalOriginalActualFairTraceChain F hInput n).member
  obtain ⟨g, hg⟩ :=
    globalOriginalActualFairNativeLimit_extend_fullAgeDiagram
      F hInput
      A (globalOriginalActualFairTraceChain F hInput n).model
      hAge i j₁
  exact ⟨n, i, g, hi, hg⟩

end AllThoseRamseyClasses.Lifts
