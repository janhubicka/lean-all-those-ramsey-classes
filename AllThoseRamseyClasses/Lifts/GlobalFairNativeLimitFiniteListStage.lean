import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitTwoSidedStage
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainCoherence

/-!
# Track F: finite-list FULL back-and-forth extension

The certified two-sided stage step deals with one prescribed pair
of vertices of the *actual* native fair direct limit M.  By
induction on a finite list of such pairs, we now extend any FULL
embedding of an actual finite stage to a later stage so that:

* every first coordinate of the list lies in the CANONICAL image
  of the new stage;
* every second coordinate lies in the IMAGE of the new FULL map;
* the new FULL map agrees with the old map along the actual FULL
  stage transition.

The proof uses the native cocone and exact all-stage composition,
not an unproved Fraïssé automorphism or a merely relational
substructure. This finite-list statement is the combinatorial
interface for the next countable-recursion construction.

All claims remain conditional on GlobalOriginalFiniteFraisseInput,
including its still-open unrestricted reducible-source shadow-
avoidance hypothesis. The frozen numbered 2019 manuscript is
unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any finite list of source/target vertex requests can be met
simultaneously by extending one actual finite-stage FULL embedding.
The canonical image covers all the source requests; the resulting
full stage map hits all target requests. The map continues to agree
with the original map on the entire original stage. -/
theorem globalOriginalActualFairNativeLimit_finiteList_twoSided_stage
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
    ∃ (n : ℕ) (hmn : m ≤ n)
      (g : Structure.Embedding
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
  induction pairs generalizing m f with
  | nil =>
      refine ⟨m, le_refl m, f, ?_, ?_⟩
      · intro p hp
        simp at hp
      · intro a
        rw [globalOriginalFiniteTraceChainLE_self]
        rfl
  | cons p ps ih =>
      let representatives := globalOriginalRepresentativePrefix F hInput
      let diagrams := globalOriginalExtensionDiagramPrefix F hInput
      obtain ⟨n, hmn, g, xn, yn, hxn, hyn, hgm⟩ :=
        globalOriginalActualFairNativeLimit_twoSided_stage_step
          F hInput m f p.1 p.2
      obtain ⟨k, hnk, gk, hps, hgk⟩ := ih n g
      have hmk : m ≤ k := le_trans hmn hnk
      refine ⟨k, hmk, gk, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with heq | htail
        · subst q
          let e := globalOriginalFiniteTraceChainLE
            F hInput representatives diagrams n k hnk
          refine ⟨e xn, e yn, ?_, ?_⟩
          · have hcocone := globalOriginalTraceFullLimitIncl_comp
              F hInput representatives diagrams n k hnk
            have hp :=
              congrArg
                (fun v : Structure.Embedding
                  (globalOriginalActualFairTraceChain F hInput n).model
                  (globalOriginalActualFairNativeLimit F hInput) =>
                    v xn) hcocone
            exact hp.trans hxn
          · exact (hgk yn).trans hyn
        · exact hps q htail
      · intro a
        have hcomp :=
          congrArg
            (fun e : Structure.Embedding
              (globalOriginalActualFairTraceChain F hInput m).model
              (globalOriginalActualFairTraceChain F hInput k).model =>
                e a)
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
          _ = g ((globalOriginalFiniteTraceChainLE
                F hInput representatives diagrams m n hmn) a) :=
              hgk ((globalOriginalFiniteTraceChainLE
                F hInput representatives diagrams m n hmn) a)
          _ = f a := hgm a

end AllThoseRamseyClasses.Lifts
