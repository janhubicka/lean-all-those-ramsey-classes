import AllThoseRamseyClasses.Lifts.GlobalFiniteFraisseCofinalScheduler
import AllThoseRamseyClasses.Lifts.GlobalFiniteFraisseExtensionScheduler
import AllThoseRamseyClasses.Lifts.GlobalCountableFraisseExtensionDiagrams

/-!
# Track F: a real finite Fraisse stage meeting cofinality and extension demands

The preceding verified modules separately build:
* finite cofinal JEP extensions containing finitely many actual
  maximal-trace representatives;
* finite strong-amalgamation extensions realizing ALL full root copies
  of ONE specified diagram A ↪ B.

This module first iterates the second construction over any FINITE
list of actual labelled extension diagrams. It then combines it with
the first construction. The resulting ONE finite age member T has:
1. a FULL embedding of the initial finite age member X;
2. a FULL copy of every listed finite age representative;
3. for every listed diagram A ↪ B, EVERY copy A ↪ X extends to
   a genuine FULL copy B ↪ T over the prescribed copy of X.

The root embeddings in (3) are over the INITIAL X, not arbitrary
copies appearing later in T. This is exactly the finite-stage
invariant needed by a diagonal Fraisse-chain construction. The
next stage schedules newly appearing copies again. No infinite
direct limit or global homogeneity is claimed here.

All maps are actual full function/value-fibre preserving embeddings
of the ORIGINAL root-injective maximal global-piece lift; shadow
avoidance remains embedded in the conditional finite-age input.
The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A finite list of actual representative extension diagrams
can be realized simultaneously over ALL initial root copies.
Every finite step uses genuine full strong amalgamation; the
previous full embeddings carry all earlier witnesses forward. -/
theorem globalOriginalFiniteFraisseInput_realizeFiniteDiagrams
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VX : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X)
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C) T ∧
      ∃ (jX : Structure.Embedding X T),
        ∀ (d : GlobalOriginalFiniteTraceDiagram F),
          d ∈ diagrams →
          ∀ f : Structure.Embedding d.1.2.1 X,
            ∃ (jB : Structure.Embedding d.2.1.2.1 T),
              ∀ a, jB (d.2.2 a) = jX (f a) := by
  classical
  induction diagrams with
  | nil =>
      refine ⟨VX, X, hX, Structure.Embedding.id X, ?_⟩
      intro d hd f
      simp at hd
  | cons d tail ih =>
      obtain ⟨VY, Y, hY, jX, hTail⟩ := ih
      obtain ⟨VT, T, hT, jY, hD⟩ :=
        globalOriginalMaximalTraceAge_realizeAllRootCopies
          F hInput d.1.2.1 d.2.1.2.1 Y d.2.1.2.2 hY d.2.2
      refine ⟨VT, T, hT, jY.comp jX, ?_⟩
      intro e he f
      rcases List.mem_cons.mp he with hEq | hIn
      · subst e
        obtain ⟨kB, hk⟩ := hD (jX.comp f)
        refine ⟨kB, ?_⟩
        intro a
        change kB (d.2.2 a) = jY (jX (f a))
        exact hk a
      · obtain ⟨kB, hk⟩ := hTail e hIn f
        refine ⟨jY.comp kB, ?_⟩
        intro a
        change jY (kB (e.2.2 a)) = jY (jX (f a))
        exact congrArg jY (hk a)

/-- ONE complete finite Fraisse stage: jointly embed finitely
many labelled representative objects, then fulfill finitely many
labelled extension diagrams on EVERY full root copy in the
original stage X. All original structures and intermediate
witnesses are genuine age members, and all maps are FULL.

This is independent of the yet-unverified countable direct limit
and faithful first-order graph model; its only class-theoretic
input is the explicit finite-age record. -/
theorem globalOriginalFiniteFraisseInput_realizeCofinalAndDiagrams
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VX : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C) T ∧
      ∃ (jX : Structure.Embedding X T),
        (∀ P : GlobalOriginalFiniteTraceRepresentatives F,
          P ∈ representatives →
            ∃ (_jP : Structure.Embedding P.2.1 T), True) ∧
        (∀ (d : GlobalOriginalFiniteTraceDiagram F),
          d ∈ diagrams →
          ∀ f : Structure.Embedding d.1.2.1 X,
            ∃ (jB : Structure.Embedding d.2.1.2.1 T),
              ∀ a, jB (d.2.2 a) = jX (f a)) := by
  classical
  obtain ⟨VY, Y, hY, jX, hReps⟩ :=
    globalOriginalFiniteFraisseInput_jointEmbedFiniteRepresentatives
      F hInput X hX representatives
  obtain ⟨VT, T, hT, jY, hDiagrams⟩ :=
    globalOriginalFiniteFraisseInput_realizeFiniteDiagrams
      F hInput Y hY diagrams
  refine ⟨VT, T, hT, jY.comp jX, ?_, ?_⟩
  · intro P hP
    obtain ⟨kP, _⟩ := hReps P hP
    exact ⟨jY.comp kP, True.intro⟩
  · intro d hd f
    obtain ⟨kB, hk⟩ := hDiagrams d hd (jX.comp f)
    refine ⟨kB, ?_⟩
    intro a
    change kB (d.2.2 a) = jY (jX (f a))
    exact hk a

end AllThoseRamseyClasses.Lifts
