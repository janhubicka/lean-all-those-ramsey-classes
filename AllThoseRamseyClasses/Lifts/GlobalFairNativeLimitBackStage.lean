import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteCover
import AllThoseRamseyClasses.Lifts.GlobalActualFairFraisseFiniteExtension
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFullLimitCocone

/-!
# Track F: finite-stage BACK extension in the actual native fair limit

The Forth lemma extends the *domain* of a FULL map X_m ↪ M so
that its canonical source stage contains any prescribed limit
vertex. Here we prove the genuinely different BACK lemma:
extend an arbitrary FULL f : X_m ↪ M to a later stage map
g : X_N ↪ M whose IMAGE contains a prescribed target vertex y.

It is invalid to demand that the finite age extension property
alone force an arbitrary newly chosen g to hit y. We instead:

1. FULL-factor f through an actual finite stage X_i.
2. Find a finite-stage representative of y; advance both to
   t = max(i,k). Obtain a FULL map j : X_m ↪ X_t so that
   u_t ∘ j = f and y = u_t(y_t).
3. Apply the VERIFIED fair finite-stage diagram extension to
   j : X_m ↪ X_t over the identity on the actual source stage
   X_m. This builds h : X_t ↪ X_(n+1) such that
   h ∘ j is the canonical stage transition.
4. Apply the native-limit finite FULL age-extension theorem to
   h using the CANONICAL inclusion u_t : X_t ↪ M, obtaining
   g : X_(n+1) ↪ M with g ∘ h = u_t.
5. Consequently g(h(y_t)) = y while g extends f along the
   canonical stage transition.

All arrows are FULL embeddings of the native partial,
possibly multivalued functional language. No first-order-only
maps, weak images, or new shadow-avoidance axiom is introduced.
The result is conditional on GlobalOriginalFiniteFraisseInput.
The numbered 2019 manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The BACK stage-extension property: an arbitrary FULL copy
of a finite fair-chain stage in the actual native limit extends
along a later canonical full stage map so that the new copy's
IMAGE contains any prescribed limit vertex y.

This is the range counterpart of the Forth stage extension
and is the key genuinely functional back-and-forth step. -/
theorem globalOriginalActualFairNativeLimit_back_stage_step
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (m : ℕ)
    (f : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairNativeLimit F hInput))
    (y : (GlobalOriginalTraceFirstOrderDirectLimit F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput))) :
    ∃ (N : ℕ) (hmN : m ≤ N)
      (g : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput N).model
        (globalOriginalActualFairNativeLimit F hInput))
      (z : (globalOriginalActualFairTraceChain F hInput N).Carrier),
      g z = y ∧
      ∀ a : (globalOriginalActualFairTraceChain F hInput m).Carrier,
        g ((globalOriginalFiniteTraceChainLE
          F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput)
          m N hmN) a) = f a := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  letI : Finite (globalOriginalActualFairTraceChain F hInput m).Carrier :=
    (globalOriginalActualFairTraceChain F hInput m).member.1
  obtain ⟨i, ji, hfi⟩ :=
    globalOriginalTraceNativeLimit_finiteFullFactor
      F hInput representatives diagrams
      (globalOriginalActualFairTraceChain F hInput m).model f
  obtain ⟨k, ys, hys⟩ :=
    globalOriginalActualFairNativeLimit_finiteFamily_fullStageCover
      F hInput (fun (_ : PUnit) => y)
  have hCanonical (r s : ℕ) (hrs : r ≤ s)
      (a : (globalOriginalActualFairTraceChain F hInput r).Carrier) :
      (globalOriginalTraceFullLimitIncl F hInput
        representatives diagrams s)
        ((globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams r s hrs) a) =
      (globalOriginalTraceFullLimitIncl F hInput
        representatives diagrams r) a := by
    have h :=
      globalOriginalTraceFullLimitIncl_comp
        F hInput representatives diagrams r s hrs
    exact congrArg
      (fun e : Structure.Embedding
        (globalOriginalActualFairTraceChain F hInput r).model
        (globalOriginalActualFairNativeLimit F hInput) => e a) h
  let t := max i k
  have hit : i ≤ t := Nat.le_max_left i k
  have hkt : k ≤ t := Nat.le_max_right i k
  let jit : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairTraceChain F hInput t).model :=
    (globalOriginalFiniteTraceChainLE F hInput
      representatives diagrams i t hit).comp ji
  have hfjt (a : (globalOriginalActualFairTraceChain F hInput m).Carrier) :
      (globalOriginalTraceFullLimitIncl F hInput
        representatives diagrams t) (jit a) = f a := by
    calc
      (globalOriginalTraceFullLimitIncl F hInput
        representatives diagrams t) (jit a) =
          (globalOriginalTraceFullLimitIncl F hInput
            representatives diagrams i) (ji a) :=
        hCanonical i t hit (ji a)
      _ = f a := hfi a
  let yt : (globalOriginalActualFairTraceChain F hInput t).Carrier :=
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams k t hkt) (ys PUnit.unit)
  have hyt :
      (globalOriginalTraceFullLimitIncl
        F hInput representatives diagrams t) yt = y := by
    calc
      (globalOriginalTraceFullLimitIncl F hInput
        representatives diagrams t) yt =
          (globalOriginalTraceFullLimitIncl F hInput
            representatives diagrams k) (ys PUnit.unit) :=
        hCanonical k t hkt (ys PUnit.unit)
      _ = y := hys PUnit.unit
  have htAge :
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C)
        (globalOriginalActualFairTraceChain F hInput t).model :=
    (globalOriginalActualFairTraceChain F hInput t).member
  obtain ⟨n, hmn, h, hh⟩ :=
    globalOriginalActualFairTraceChain_extend_arbitraryFullAgeDiagram
      F hInput
      (globalOriginalActualFairTraceChain F hInput m).model
      (globalOriginalActualFairTraceChain F hInput t).model
      htAge jit m
      (Structure.Embedding.id
        (globalOriginalActualFairTraceChain F hInput m).model)
  have hChain
      (a : (globalOriginalActualFairTraceChain F hInput m).Carrier) :
      h (jit a) =
        (globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams m (n + 1)
          (Nat.le_succ_of_le hmn)) a := by
    calc
      h (jit a) =
        (globalOriginalActualFairTraceChainStep F hInput n)
          ((globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams m n hmn) a) := by
              simpa using hh a
      _ = (globalOriginalFiniteTraceChainLE F hInput
            representatives diagrams m (n + 1)
            (Nat.le_succ_of_le hmn)) a := by
              rw [globalOriginalFiniteTraceChainLE_succ
                F hInput representatives diagrams m n hmn]
              rfl
  have hnAge :
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C)
        (globalOriginalActualFairTraceChain F hInput (n + 1)).model :=
    (globalOriginalActualFairTraceChain F hInput (n + 1)).member
  obtain ⟨g, hg⟩ :=
    globalOriginalActualFairNativeLimit_extend_fullAgeDiagram
      F hInput
      (globalOriginalActualFairTraceChain F hInput t).model
      (globalOriginalActualFairTraceChain F hInput (n + 1)).model
      hnAge h
      (globalOriginalTraceFullLimitIncl F hInput
        representatives diagrams t)
  refine ⟨n + 1, Nat.le_succ_of_le hmn, g, h yt, ?_, ?_⟩
  · exact (hg yt).trans hyt
  · intro a
    calc
      g ((globalOriginalFiniteTraceChainLE F hInput
        representatives diagrams m (n + 1)
        (Nat.le_succ_of_le hmn)) a) =
          g (h (jit a)) := congrArg g (hChain a).symm
      _ = (globalOriginalTraceFullLimitIncl F hInput
            representatives diagrams t) (jit a) := hg (jit a)
      _ = f a := hfjt a

end AllThoseRamseyClasses.Lifts
