import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Track C: weak local tests with U-irreducible ambient closure hulls

For an arbitrary exact weak vertex set S in a U-closed tagged
candidate C, the U-closure HULL of S is an auxiliary set, not a
replacement for the weak carrier S.

If this hull is U-irreducible, corrected (4b) says its induced
structure is in canonical K(H), and a genuine H target therefore
contains the exact weak test C.induce S by its ordinary full
relational inclusion. Assuming all K(H)-members are ordinary
irreducible, this full embedding gives the required ambient-relative
H-completion with the original exact source S.

Consequently the corrected local-completion implication at fixed
B,C0,n is equivalent to the analogous implication that requests
completions only for S whose ambient U-closure hull is U-REDUCIBLE.
This is strictly a reduction of the required *antecedent checks*:
it does not prove that every such reducible-hull test is completable,
or derive the literal original intrinsic local class assumption.

Input and output functions are genuine set-valued partial functions
in the canonical targets. The ambient source uses tagged OLD
relations and retains all domain masks. There is no surreptitious
substitution of an intrinsic whole-fibre weak test for C.induce S.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- Every exact weak S with U-irreducible induced ambient closure hull
has a genuine H-valued ambient-relative completion, independent of
local finiteness. The hull is used only to select the H target;
the completion map's source remains C.induce S on exactly S. -/
theorem genuineTagged2019_uIrredHull_has_relativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hKIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → E.Irreducible)
    (S : Set V)
    (hHullIrred :
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce
          (UClosureHull ((L.withParts Parts).wholeMaskClosureRules Parts)
            C S))) :
    HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S) := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let Hull : Set V := UClosureHull rules C S
  have hHullClosed : IsUClosed rules (C.induce Hull) :=
    hClosed.induce_UClosureHull S
  have hHullK : canonicalGenuineTagged2019Class H (C.induce Hull) :=
    hCovered Hull hHullClosed hHullIrred
  obtain ⟨hFinite, Target, targetPart, hH, hTr, hEq⟩ := hHullK
  letI : Finite Hull := hFinite
  let e : RelStructure.Embedding (C.induce S) (C.induce Hull) := {
    toFun := fun x => ⟨x.1, subset_UClosureHull rules C S x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Hull => z.1) hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  have hKTarget :
      canonicalGenuineTagged2019Class H
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)) :=
    canonicalGenuineTagged2019Class_mem H Target targetPart hH hTr
  have hIrredTarget :
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)).Irreducible :=
    hKIrred _ hKTarget
  have hEmbedding : RelStructure.Embedding
      (C.induce S)
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) := by
    rw [← hEq]
    exact e
  have hMap : IsInducedClosedUHomomorphismEmbedding rules
      (C.induce S)
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) hEmbedding.toFun :=
    (hEmbedding.isClosedUHomomorphismEmbedding rules).toInducedClosed
  exact ⟨Hull, hFinite, Target, targetPart, hH, hTr,
    hIrredTarget, hEmbedding.toFun, hMap⟩

/-- Candidate-local corrected 2019 axiom in which completion hypotheses
are imposed only for exact weak S with U-reducible closure hull.
The tested carrier S, global candidate C, cutoff n, control C0,
and demanded B-copywise completion are literally unchanged. -/
def GenuinePartiteTagged2019ReducibleHullLocalCompletionAt
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) : Prop :=
  ∀ {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
    IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C →
    (C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p) →
    CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C →
    (∀ S : Finset X, S.card ≤ n →
      ¬ IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce
          (UClosureHull
            ((L.withParts Parts).wholeMaskClosureRules Parts)
            C (↑S : Set X))) →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set X))) →
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

/-- Under the actual corrected ambient irreducibility hypothesis on
canonical targets, requiring all exact weak H-relative completion
premises is EQUIVALENT to requiring them only at weak tests whose
U-closure hull is not U-irreducible. No size or map changes. -/
theorem genuineTagged2019_localCompletion_iff_reducibleHulls
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ)
    (hKIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → E.Irreducible) :
    GenuinePartiteTagged2019LocalCompletionAt H B C0 n ↔
      GenuinePartiteTagged2019ReducibleHullLocalCompletionAt H B C0 n := by
  constructor
  · intro hAll X hX C hClosed hControl hCovered hHard
    apply hAll C hClosed hControl hCovered
    intro S hSize
    by_cases hHull :
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce
            (UClosureHull
              ((L.withParts Parts).wholeMaskClosureRules Parts)
              C (↑S : Set X)))
    · exact genuineTagged2019_uIrredHull_has_relativeCompletion
        H C hClosed hCovered hKIrred (↑S : Set X) hHull
    · exact hHard S hSize hHull
  · intro hHard X hX C hClosed hControl hCovered hAll
    apply hHard C hClosed hControl hCovered
    intro S hSize _
    exact hAll S hSize

/-- In the original corrected class theorem the extra target
irreducibility premise follows from K(H)⊆R and R irreducible. -/
theorem genuineTagged2019_localCompletion_iff_reducibleHulls_of_ambient
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hRIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hSub : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → R E)
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) :
    GenuinePartiteTagged2019LocalCompletionAt H B C0 n ↔
      GenuinePartiteTagged2019ReducibleHullLocalCompletionAt H B C0 n :=
  genuineTagged2019_localCompletion_iff_reducibleHulls H B C0 n
    (fun E hK => hRIrred E (hSub E hK))

end AllThoseRamseyClasses.Published
