import AllThoseRamseyClasses.Lifts.GlobalOriginalFraisseDiagramRepresentatives
import AllThoseRamseyClasses.Lifts.GlobalFullDiagramExtensionTransport
import AllThoseRamseyClasses.Lifts.GlobalActualFairFraisseChain
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainAllStages

/-!
# Track F: exact finite-stage extension property for arbitrary FULL age diagrams

The original maximal-trace finite Fraïssé age has an ACTUAL fair
chain (verified #928) whose stages are finite and whose transitions
are genuine FULL functional embeddings. The fair schedule revisits
every representative extension diagram at all sufficiently late stages.

The representative-diagram transport (#950) and its full witness
transfer (#952) turn this into the honest finite-stage extension
property for an ARBITRARY finite FULL age extension i:A↪B:

For any current stage X_m and any FULL root embedding f:A↪X_m,
there is a later stage X_{n+1}, with n≥m, and a genuine FULL
embedding g:B↪X_{n+1} extending f via the actual full
transition X_m↪X_n↪X_{n+1}.

Every function-value set is preserved ENTIRELY; neither finite
generation bounds nor a weak EHN map nor any fictitious
one-point extension principle is used.

This is the core FINITE stage property needed to prove the
extension property of the eventual native direct limit.
The proof is conditional on the certified finite-age input
(which retains global shadow avoidance for arbitrary reducible
forbidden sources). It does NOT construct the limit, or assert
age equality, ultrahomogeneity, or the full Ramsey theorem.
The numbered 2019 ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual fair finite maximal-trace chain has the full
finite-stage EXTENSION PROPERTY for all finite full age
diagrams A↪B, not only the chosen labelled representatives.

For any full A-copy f in stage m, find n≥m and a full
B-copy g in stage n+1 that agrees with the canonical
full m-to-(n+1) transition on the given A-copy.

No limit object is assumed in the statement or proof. -/
theorem globalOriginalActualFairTraceChain_extend_arbitraryFullAgeDiagram
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VA VB : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (hB : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) B)
    (i : Structure.Embedding A B)
    (m : ℕ)
    (f : Structure.Embedding A
      (globalOriginalActualFairTraceChain F hInput m).model) :
    ∃ (n : ℕ) (hmn : m ≤ n)
      (g : Structure.Embedding B
        (globalOriginalActualFairTraceChain F hInput (n + 1)).model),
      ∀ x : VA,
        g (i x) =
          (globalOriginalActualFairTraceChainStep F hInput n)
            ((globalOriginalFiniteTraceChainLE
              F hInput
              (globalOriginalRepresentativePrefix F hInput)
              (globalOriginalExtensionDiagramPrefix F hInput)
              m n hmn) (f x)) := by
  obtain ⟨d, a, b, ha, hb, hSquare⟩ :=
    globalOriginalFiniteTraceDiagram_represents_fullExtension
      F hInput A B hB i
  obtain ⟨N, hN⟩ :=
    globalOriginalActualFairTraceChain_eventually_extends
      F hInput d
  let n := max m N
  have hmn : m ≤ n := Nat.le_max_left m N
  have hNn : N ≤ n := Nat.le_max_right m N
  let emn : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairTraceChain F hInput n).model :=
    globalOriginalFiniteTraceChainLE
      F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput)
      m n hmn
  let step := globalOriginalActualFairTraceChainStep F hInput n
  let fN : Structure.Embedding A
      (globalOriginalActualFairTraceChain F hInput n).model :=
    emn.comp f
  let root : Structure.Embedding d.1.2.1
      (globalOriginalActualFairTraceChain F hInput n).model :=
    fN.comp a
  obtain ⟨jQ, hRoot⟩ := hN n hNn root
  let fNext : Structure.Embedding A
      (globalOriginalActualFairTraceChain F hInput (n + 1)).model :=
    step.comp fN
  have hDiagram : ∀ p, jQ (d.2.2 p) = fNext (a p) := by
    intro p
    exact hRoot p
  obtain ⟨g, hg⟩ :=
    fullExtensionWitness_transportFromSurjectiveSquare
      d.2.2 a b ha hb i hSquare fNext jQ hDiagram
  refine ⟨n, hmn, g, ?_⟩
  intro x
  exact hg x

end AllThoseRamseyClasses.Lifts
