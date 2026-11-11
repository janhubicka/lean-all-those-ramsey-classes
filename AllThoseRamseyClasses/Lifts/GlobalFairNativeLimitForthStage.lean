import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteCover
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFullLimitCocone

/-!
# Track F: finite-stage forth extension in the native fair limit

Given any FULL embedding f : X_m ↪ M of an actual finite stage
into the actual native fair limit, and any arbitrary vertex x
of M, find a later finite stage X_n whose *canonical* image
contains x, and a FULL embedding g : X_n ↪ M extending f
along the true full finite-stage transition X_m ↪ X_n.

The proof is two independent steps:
(1) the finite FULL stage-cover property locates x in a stage,
    then moves it forward to a stage n >= m using the full
    directed-limit cocone;
(2) the arbitrary finite FULL age-extension theorem supplies
    g extending f along the actual canonical stage map.

Importantly, the theorem does NOT require the image of g
to contain the given x: the canonical inclusion of X_n
contains x. This is the correct 'forth' step for extending
finite partial automorphisms, not an unjustified onto-target
claim. The complementary 'back' step is separate.

Conditional on the original finite Fraisse input; no global
shadow avoidance, ultrahomogeneity or unrestricted Ramsey.
The numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any FULL embedding of a finite actual fair-chain stage into
the native limit extends along a later FULL stage whose CANONICAL
image covers an arbitrarily prescribed limit vertex.

This is the finite-domain 'forth' extension step for an eventual
back-and-forth argument. The extended map is a genuine FULL
functional embedding (not merely a relational graph embedding). -/
theorem globalOriginalActualFairNativeLimit_forth_stage_step
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (m : ℕ)
    (f : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairNativeLimit F hInput))
    (x : (globalOriginalActualFairNativeLimit F hInput).Carrier) :
    ∃ (n : ℕ) (hmn : m ≤ n)
      (y : (globalOriginalActualFairTraceChain F hInput n).Carrier)
      (g : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput n).model
        (globalOriginalActualFairNativeLimit F hInput)),
      (globalOriginalTraceFullLimitIncl
        F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        n) y = x ∧
      ∀ a : (globalOriginalActualFairTraceChain F hInput m).Carrier,
        g ((globalOriginalFiniteTraceChainLE
          F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput)
          m n hmn) a) = f a := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨i, ys, hys⟩ :=
    globalOriginalActualFairNativeLimit_finiteFamily_fullStageCover
      F hInput (fun (_ : PUnit) => x)
  let n := max m i
  have hmn : m ≤ n := Nat.le_max_left m i
  have hin : i ≤ n := Nat.le_max_right m i
  let y :
      (globalOriginalActualFairTraceChain F hInput n).Carrier :=
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams i n hin) (ys PUnit.unit)
  have hCocone :
      (globalOriginalTraceFullLimitIncl
        F hInput representatives diagrams n) y =
      (globalOriginalTraceFullLimitIncl
        F hInput representatives diagrams i) (ys PUnit.unit) := by
    have h :=
      globalOriginalTraceFullLimitIncl_comp
        F hInput representatives diagrams i n hin
    have ha :=
      congrArg
        (fun e : Structure.Embedding
          (globalOriginalActualFairTraceChain F hInput i).model
          (globalOriginalActualFairNativeLimit F hInput) =>
            e (ys PUnit.unit)) h
    exact ha
  have hy :
      (globalOriginalTraceFullLimitIncl
        F hInput representatives diagrams n) y = x :=
    hCocone.trans (hys PUnit.unit)
  have hStage :
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C)
        (globalOriginalActualFairTraceChain F hInput n).model :=
    (globalOriginalFiniteTraceChain F hInput representatives diagrams n).member
  obtain ⟨g, hg⟩ :=
    globalOriginalActualFairNativeLimit_extend_fullAgeDiagram
      F hInput
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairTraceChain F hInput n).model
      hStage
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n hmn)
      f
  exact ⟨n, hmn, y, g, hy, hg⟩

end AllThoseRamseyClasses.Lifts
