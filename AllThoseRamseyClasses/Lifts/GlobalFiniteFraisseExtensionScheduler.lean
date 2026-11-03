import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3FraisseInput
import PartiteConstruction.Structure.Basic

/-!
# Track F — schedule finitely many genuine Fraïssé extension requests

A finite-age Fraïssé construction repeatedly needs to extend a
current finite member X so that each requested full root embedding
f : A ↪ X extends along a prescribed finite full extension i : A ↪ B.

The existing original maximal-trace finite-age theorem gives ACTUAL
strong amalgamation with exact overlap. This module uses it to prove:

* any finite LIST of requests f : A ↪ X can all be met in ONE finite
  age extension T of X, preserving earlier requests;
* since both A and X are finite, ALL full copies of A in X can be
  handled simultaneously in one finite T.

This is a verified one-stage FINITE extension-scheduler lemma; it
does NOT assert a countable direct limit, that all countably many
extension types have been scheduled, or ultrahomogeneity.

Every embedding is a FULL native-lifted functional embedding,
including reflection of added relations and equality of complete
old partial/set-valued function fibres. No weak HE maps, root
injectivization, or arbitrary closure-hull substitutions are used.

The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One strong-amalgamation construction can realize an arbitrary
finite list of extension demands along a FIXED finite full
extension A ↪ B inside a finite age member X.

All demands are met by full embeddings into the SAME actual finite
age member T. Distinct requested embeddings may overlap; no
artificial pairwise-disjointness hypothesis is required. -/
theorem globalMaximalTraceAge_realizeFiniteExtensionRequests
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hCore : GlobalFiniteMaximalTraceAmalgamationCore F K)
    {VA VB VX : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hB : IsGlobalFiniteMaximalTrace F K B)
    (hX : IsGlobalFiniteMaximalTrace F K X)
    (i : Structure.Embedding A B)
    (requests : List (Structure.Embedding A X)) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F K T ∧
      ∃ (jX : Structure.Embedding X T),
        ∀ f : Structure.Embedding A X, f ∈ requests →
          ∃ (jB : Structure.Embedding B T),
            ∀ a : VA, jB (i a) = jX (f a) := by
  classical
  induction requests with
  | nil =>
      refine ⟨VX, X, hX, Structure.Embedding.id X, ?_⟩
      intro f hf
      simp at hf
  | cons f tail ih =>
      obtain ⟨VD, D, hD, jX, hTail⟩ := ih
      let fD : Structure.Embedding A D := jX.comp f
      obtain ⟨VT, T, hT, jD, jB, hOverlap⟩ :=
        hCore.strongAmalgamation A D B hD hB fD i
      refine ⟨VT, T, hT, jD.comp jX, ?_⟩
      intro g hg
      have hh : g = f ∨ g ∈ tail := by
        simpa only [List.mem_cons] using hg
      rcases hh with hgf | hg
      · subst g
        refine ⟨jB, ?_⟩
        intro a
        have heq :=
          (hOverlap (fD a) (i a)).mpr ⟨a, rfl, rfl⟩
        change jD (jX (f a)) = jB (i a) at heq
        exact heq.symm
      · obtain ⟨kB, hkB⟩ := hTail g hg
        refine ⟨jD.comp kB, ?_⟩
        intro a
        change jD (kB (i a)) = jD (jX (g a))
        exact congrArg jD (hkB a)

/-- One step of the genuine original finite-age Fraïssé
extension schedule, conditional only on the exact previously
proved finite Fraïssé-age input record. The latter keeps
shadow avoidance explicit for unrestricted reducible sources. -/
theorem globalOriginalMaximalTraceAge_realizeFiniteExtensionRequests
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VA VB VX : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hB : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) B)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X)
    (i : Structure.Embedding A B)
    (requests : List (Structure.Embedding A X)) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C) T ∧
      ∃ (jX : Structure.Embedding X T),
        ∀ f : Structure.Embedding A X, f ∈ requests →
          ∃ (jB : Structure.Embedding B T),
            ∀ a : VA, jB (i a) = jX (f a) :=
  globalMaximalTraceAge_realizeFiniteExtensionRequests
    F (fun {W : Type} (C : Structure L W) =>
      AvoidsGlobalFunctionalEHN F C)
    hInput.finiteAgeCore A B X hB hX i requests

/-- FINITENESS of the actual old and root carriers makes the
type of FULL root embeddings A ↪ X finite. Thus one finite
strong-amalgamation iteration can solve EVERY request for a
fixed full extension A ↪ B at once.

This is the finite saturation step needed for the later
countable Fraïssé chain; it does not perform the infinite
bookkeeping or construct the limit. -/
theorem globalMaximalTraceAge_realizeAllRootCopies
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hCore : GlobalFiniteMaximalTraceAmalgamationCore F K)
    {VA VB VX : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hB : IsGlobalFiniteMaximalTrace F K B)
    (hX : IsGlobalFiniteMaximalTrace F K X)
    (i : Structure.Embedding A B) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F K T ∧
      ∃ (jX : Structure.Embedding X T),
        ∀ f : Structure.Embedding A X,
          ∃ (jB : Structure.Embedding B T),
            ∀ a : VA, jB (i a) = jX (f a) := by
  classical
  letI : Finite VB := hB.1
  letI : Finite VA := Finite.of_injective i i.injective
  letI : Finite VX := hX.1
  letI : Fintype (Structure.Embedding A X) :=
    Fintype.ofFinite _
  obtain ⟨VT, T, hT, jX, hRequests⟩ :=
    globalMaximalTraceAge_realizeFiniteExtensionRequests
      F K hCore A B X hB hX i (Finset.univ.toList)
  exact ⟨VT, T, hT, jX,
    fun f => hRequests f (by simp)⟩

/-- Full original age version of finite saturation for ALL
copies of one fixed extension diagram A ↪ B. Under irreducible
forbidden sources this is unconditional once the input record
has been constructed by the certified special-case theorem. -/
theorem globalOriginalMaximalTraceAge_realizeAllRootCopies
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VA VB VX : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hB : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) B)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X)
    (i : Structure.Embedding A B) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (C : Structure L W) =>
          AvoidsGlobalFunctionalEHN F C) T ∧
      ∃ (jX : Structure.Embedding X T),
        ∀ f : Structure.Embedding A X,
          ∃ (jB : Structure.Embedding B T),
            ∀ a : VA, jB (i a) = jX (f a) :=
  globalMaximalTraceAge_realizeAllRootCopies
    F (fun {W : Type} (C : Structure L W) =>
      AvoidsGlobalFunctionalEHN F C)
    hInput.finiteAgeCore A B X hB hX i

end AllThoseRamseyClasses.Lifts
