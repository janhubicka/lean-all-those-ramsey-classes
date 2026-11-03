import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3FraisseInput

/-!
# Track F: finite JEP scheduler for the original maximal-trace age

An actual Fraïssé chain needs TWO independent finite requirements:
(1) a cofinality step which embeds each enumerated finite age
representative somewhere in the chain; and (2) the extension
property for all requested copies of a finite root diagram.

The extension part is handled separately by the finite strong-AP
scheduler (Track F #825). This file proves the cofinality part:

For a finite list of genuinely finite age representatives, there
is ONE finite original maximal-trace age member containing FULL
copies of the current stage and every listed representative.
Every old partial/set-valued function fibre and every added
global piece-class relation is respected FULLY.

The proof iterates the verified finite maximal-trace JEP, composing
earlier full embeddings at each step. No weak EHN maps, hidden
arbitrary free amalgams, shadow-avoidance bypass or countable
direct limit is asserted here.

The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Finitely many actual representatives may be embedded FULLY into
ONE larger finite age member along with an arbitrary starting
finite age structure X. A different representative can have a
different carrier Fin n; no global bound on sizes is needed.

The theorem is conditional on the already checked exact finite-age
input, which retains native JEP and original shadow-free
amalgamation as explicit hypotheses in the unrestricted case. -/
theorem globalOriginalFiniteFraisseInput_jointEmbedFiniteRepresentatives
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VX : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F)) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C) T ∧
      ∃ (jX : Structure.Embedding X T),
        ∀ P : GlobalOriginalFiniteTraceRepresentatives F,
          P ∈ representatives →
            ∃ (jP : Structure.Embedding P.2.1 T), True := by
  classical
  induction representatives with
  | nil =>
      refine ⟨VX, X, hX, Structure.Embedding.id X, ?_⟩
      intro P hP
      simp at hP
  | cons P tail ih =>
      obtain ⟨VT, T, hT, jX, hTail⟩ := ih
      obtain ⟨VW, W, hW, jT, jP, _⟩ :=
        hInput.finiteAgeCore.jointEmbedding
          T P.2.1 hT P.2.2
      refine ⟨VW, W, hW, jT.comp jX, ?_⟩
      intro Q hQ
      have hMem : Q = P ∨ Q ∈ tail := by
        simpa only [List.mem_cons] using hQ
      rcases hMem with hEq | hTailMem
      · subst Q
        exact ⟨jP, True.intro⟩
      · obtain ⟨jQ, _⟩ := hTail Q hTailMem
        exact ⟨jT.comp jQ, True.intro⟩

end AllThoseRamseyClasses.Lifts
