import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitForthStage
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitBackStage

/-!
# Track F: one two-sided FULL stage-extension step

The verified mathematical forward/backward stage mechanisms may
be used consecutively: first cover an arbitrary prescribed source
vertex by a canonical finite-stage image, and then force an arbitrary
prescribed target vertex into the range of a FULL stage embedding.
The second step extends the first, so source coverage is retained
by the native FULL cocone identity.

This provides the exact local alternating step for countable
back-and-forth, without assuming any eventual homogeneous limit
or swapping genuine FULL embeddings for relational graph maps.

The resulting theorem remains CONDITIONAL on
GlobalOriginalFiniteFraisseInput F. Unrestricted reducible-source
shadow avoidance / the original 2019 Claim 2 is separate.

The numbered manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Simultaneously extend an arbitrary FULL finite-stage map in
the actual native fair limit to cover one prescribed source
vertex in the CANONICAL image and one prescribed target vertex
in the IMAGE of the new full map.

All finite-stage maps appearing here are genuine FULL structural
embeddings: every set-valued partial-function fibre is preserved
in both directions, including nullaries and empty fibres. -/
theorem globalOriginalActualFairNativeLimit_twoSided_stage_step
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (m : ℕ)
    (f : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairNativeLimit F hInput))
    (x y : GlobalOriginalTraceFirstOrderDirectLimit F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput)) :
    ∃ (k : ℕ) (hmk : m ≤ k)
      (g : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput k).model
        (globalOriginalActualFairNativeLimit F hInput))
      (xk yk : (globalOriginalActualFairTraceChain F hInput k).Carrier),
      (globalOriginalTraceFullLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) k) xk = x ∧
      g yk = y ∧
      ∀ a : (globalOriginalActualFairTraceChain F hInput m).Carrier,
        g ((globalOriginalFiniteTraceChainLE F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput)
          m k hmk) a) = f a := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨n, hmn, xn, gn, hxn, hgn⟩ :=
    globalOriginalActualFairNativeLimit_forth_stage_step F hInput m f x
  obtain ⟨k, hnk, gk, yk, hyk, hgk⟩ :=
    globalOriginalActualFairNativeLimit_back_stage_step F hInput n gn y
  let xk : (globalOriginalActualFairTraceChain F hInput k).Carrier :=
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams n k hnk) xn
  have hxk :
      (globalOriginalTraceFullLimitIncl
        F hInput representatives diagrams k) xk = x := by
    have hcocone := globalOriginalTraceFullLimitIncl_comp
      F hInput representatives diagrams n k hnk
    have hp :=
      congrArg
        (fun e : Structure.Embedding
          (globalOriginalActualFairTraceChain F hInput n).model
          (globalOriginalActualFairNativeLimit F hInput) => e xn)
        hcocone
    exact hp.trans hxn
  have hmk : m ≤ k := le_trans hmn hnk
  refine ⟨k, hmk, gk, xk, yk, hxk, hyk, ?_⟩
  intro a
  have hcomp :=
    congrArg
      (fun e : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput m).model
        (globalOriginalActualFairTraceChain F hInput k).model => e a)
      (globalOriginalFiniteTraceChainLE_comp
        F hInput representatives diagrams m n k hmn hnk)
  calc
    gk ((globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams m k hmk) a) =
      gk ((globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams n k hnk)
        ((globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams m n hmn) a)) :=
        congrArg gk hcomp.symm
    _ = gn ((globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams m n hmn) a) :=
      hgk ((globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n hmn) a)
    _ = f a := hgn a

end AllThoseRamseyClasses.Lifts
